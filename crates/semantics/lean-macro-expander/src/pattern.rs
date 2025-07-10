use eterned::BaseCoword;
use im::HashMap;
use lean_syn_expr::{Syntax, SyntaxKind};

use crate::error::{ExpansionError, ExpansionResult};

/// Result of pattern matching
#[derive(Debug, Clone)]
pub struct PatternMatch {
    /// Bindings from pattern variables to syntax
    pub bindings: HashMap<BaseCoword, Syntax>,
}

/// Pattern matcher for macro expansion
pub struct PatternMatcher;

impl PatternMatcher {
    /// Match a pattern against syntax
    pub fn match_pattern(
        pattern: &Syntax,
        syntax: &Syntax,
    ) -> ExpansionResult<Option<PatternMatch>> {
        let mut bindings = HashMap::new();
        if Self::match_recursive(pattern, syntax, &mut bindings)? {
            Ok(Some(PatternMatch { bindings }))
        } else {
            Ok(None)
        }
    }

    fn match_recursive(
        pattern: &Syntax,
        syntax: &Syntax,
        bindings: &mut HashMap<BaseCoword, Syntax>,
    ) -> ExpansionResult<bool> {
        match (pattern, syntax) {
            // Exact atom match
            (Syntax::Atom(p_atom), Syntax::Atom(s_atom)) => Ok(p_atom.value == s_atom.value),

            // Pattern variable (antiquotation in pattern)
            (Syntax::Node(p_node), _) if p_node.kind == SyntaxKind::SyntaxAntiquotation => {
                // Extract variable name
                if let Some(Syntax::Atom(var_name)) = p_node.children.first() {
                    // Check if already bound
                    if let Some(existing) = bindings.get(&var_name.value) {
                        // Must match existing binding
                        Self::syntax_equal(existing, syntax)
                    } else {
                        // New binding
                        bindings.insert(var_name.value.clone(), syntax.clone());
                        Ok(true)
                    }
                } else {
                    Ok(false)
                }
            }

            // Pattern splice (antiquotation with splice syntax)
            (Syntax::Node(p_node), _) if p_node.kind == SyntaxKind::SyntaxSplice => {
                // Extract variable name
                if let Some(Syntax::Atom(var_name)) = p_node.children.first() {
                    // For splices, we need to collect multiple matching elements
                    // For now, bind the whole syntax as is (this will be expanded later)
                    if let Some(existing) = bindings.get(&var_name.value) {
                        // Must match existing binding
                        Self::syntax_equal(existing, syntax)
                    } else {
                        // New binding - store as a list/sequence
                        bindings.insert(var_name.value.clone(), syntax.clone());
                        Ok(true)
                    }
                } else {
                    Ok(false)
                }
            }

            // Typed parameter pattern like x:term (parsed as App x term)
            (Syntax::Node(p_node), _)
                if p_node.kind == SyntaxKind::App && p_node.children.len() == 2 =>
            {
                // Check if this looks like a typed parameter
                if let (Some(Syntax::Atom(var_name)), Some(Syntax::Atom(_category))) =
                    (p_node.children.first(), p_node.children.get(1))
                {
                    // This is a typed parameter like x:term
                    // For now, we ignore the category and just bind the variable
                    if let Some(existing) = bindings.get(&var_name.value) {
                        Self::syntax_equal(existing, syntax)
                    } else {
                        bindings.insert(var_name.value.clone(), syntax.clone());
                        Ok(true)
                    }
                } else {
                    // Regular App node match - match as a regular node
                    if let Syntax::Node(s_node) = syntax {
                        if p_node.kind == s_node.kind
                            && p_node.children.len() == s_node.children.len()
                        {
                            for (p_child, s_child) in
                                p_node.children.iter().zip(s_node.children.iter())
                            {
                                if !Self::match_recursive(p_child, s_child, bindings)? {
                                    return Ok(false);
                                }
                            }
                            Ok(true)
                        } else {
                            Ok(false)
                        }
                    } else {
                        Ok(false)
                    }
                }
            }

            // Special handling for SyntaxQuotation patterns - unwrap them
            (Syntax::Node(p_node), _) if p_node.kind == SyntaxKind::SyntaxQuotation => {
                // A SyntaxQuotation in a pattern should match against the quoted content
                if let Some(quoted_pattern) = p_node.children.first() {
                    Self::match_recursive(quoted_pattern, syntax, bindings)
                } else {
                    Ok(false)
                }
            }

            // Node match - must have same kind and match all children
            (Syntax::Node(p_node), Syntax::Node(s_node)) => {
                if p_node.kind != s_node.kind {
                    return Ok(false);
                }

                // Check if pattern contains splices
                let has_splice = p_node.children.iter().any(|child| {
                    matches!(child, Syntax::Node(node) if node.kind == SyntaxKind::SyntaxSplice)
                });

                if has_splice {
                    // Handle splice matching - collect remaining elements
                    Self::match_with_splice(p_node, s_node, bindings)
                } else {
                    // Normal matching - must have same number of children
                    if p_node.children.len() != s_node.children.len() {
                        return Ok(false);
                    }

                    for (p_child, s_child) in p_node.children.iter().zip(s_node.children.iter()) {
                        if !Self::match_recursive(p_child, s_child, bindings)? {
                            return Ok(false);
                        }
                    }

                    Ok(true)
                }
            }

            // Missing matches missing
            (Syntax::Missing, Syntax::Missing) => Ok(true),

            // Otherwise no match
            _ => Ok(false),
        }
    }

    /// Match a pattern with splice against syntax
    fn match_with_splice(
        p_node: &lean_syn_expr::SyntaxNode,
        s_node: &lean_syn_expr::SyntaxNode,
        bindings: &mut HashMap<BaseCoword, Syntax>,
    ) -> ExpansionResult<bool> {
        let mut p_idx = 0;
        let mut s_idx = 0;

        while p_idx < p_node.children.len() {
            let p_child = &p_node.children[p_idx];

            // Check if this is a splice
            if let Syntax::Node(splice_node) = p_child {
                if splice_node.kind == SyntaxKind::SyntaxSplice {
                    // Extract variable name from splice
                    if let Some(Syntax::Atom(var_name)) = splice_node.children.first() {
                        // Collect remaining elements for the splice
                        let mut splice_elements = Vec::new();

                        // Look ahead to see how many elements we need to leave for the rest of the
                        // pattern
                        let remaining_pattern_count = p_node.children.len() - p_idx - 1;
                        let available_syntax_count = s_node.children.len() - s_idx;

                        if available_syntax_count >= remaining_pattern_count {
                            let splice_count = available_syntax_count - remaining_pattern_count;

                            // Collect elements for the splice
                            for _ in 0..splice_count {
                                if s_idx < s_node.children.len() {
                                    splice_elements.push(s_node.children[s_idx].clone());
                                    s_idx += 1;
                                }
                            }

                            // Create a node to hold the splice elements
                            let splice_result = if splice_elements.is_empty() {
                                Syntax::Missing
                            } else if splice_elements.len() == 1 {
                                splice_elements[0].clone()
                            } else {
                                // Create an App node containing all splice elements
                                Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
                                    kind: SyntaxKind::App,
                                    range: s_node.range,
                                    children: splice_elements.into(),
                                }))
                            };

                            // Bind the splice variable
                            bindings.insert(var_name.value.clone(), splice_result);
                        } else {
                            // Not enough elements to satisfy the pattern
                            return Ok(false);
                        }
                    }

                    p_idx += 1;
                    continue;
                }
            }

            // Regular matching
            if s_idx >= s_node.children.len() {
                return Ok(false);
            }

            if !Self::match_recursive(p_child, &s_node.children[s_idx], bindings)? {
                return Ok(false);
            }

            p_idx += 1;
            s_idx += 1;
        }

        // Check if we consumed all syntax elements
        Ok(s_idx == s_node.children.len())
    }

    /// Check if two syntax trees are structurally equal
    fn syntax_equal(a: &Syntax, b: &Syntax) -> ExpansionResult<bool> {
        match (a, b) {
            (Syntax::Atom(a_atom), Syntax::Atom(b_atom)) => Ok(a_atom.value == b_atom.value),
            (Syntax::Node(a_node), Syntax::Node(b_node)) => {
                if a_node.kind != b_node.kind || a_node.children.len() != b_node.children.len() {
                    return Ok(false);
                }
                for (a_child, b_child) in a_node.children.iter().zip(b_node.children.iter()) {
                    if !Self::syntax_equal(a_child, b_child)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Syntax::Missing, Syntax::Missing) => Ok(true),
            _ => Ok(false),
        }
    }
}

/// Substitute bindings into a template
pub fn substitute_template(
    template: &Syntax,
    bindings: &HashMap<BaseCoword, Syntax>,
) -> ExpansionResult<Syntax> {
    match template {
        Syntax::Atom(_) => Ok(template.clone()),
        Syntax::Missing => Ok(template.clone()),

        Syntax::Node(node) => {
            // Handle syntax quotations - substitute into their contents but keep them as
            // quotations
            if node.kind == SyntaxKind::SyntaxQuotation {
                // Substitute into the content of the quotation but keep it wrapped
                let mut new_children = Vec::new();
                for child in &node.children {
                    new_children.push(substitute_template(child, bindings)?);
                }
                return Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
                    kind: node.kind,
                    range: node.range,
                    children: new_children.into(),
                })));
            }

            // Handle antiquotations in template
            if node.kind == SyntaxKind::SyntaxAntiquotation {
                if let Some(Syntax::Atom(var_name)) = node.children.first() {
                    if let Some(bound_syntax) = bindings.get(&var_name.value) {
                        return Ok(bound_syntax.clone());
                    } else {
                        return Err(ExpansionError::InvalidAntiquotation {
                            message: format!("Unbound variable: {}", var_name.value),
                            range: node.range,
                        });
                    }
                }
            }

            // Handle splices in template
            if node.kind == SyntaxKind::SyntaxSplice {
                if let Some(Syntax::Atom(var_name)) = node.children.first() {
                    if let Some(bound_syntax) = bindings.get(&var_name.value) {
                        // For splices, we need to "explode" the bound syntax
                        // If it's a list/sequence, we should return its elements
                        // For now, just return the bound syntax as is
                        return Ok(bound_syntax.clone());
                    } else {
                        return Err(ExpansionError::InvalidAntiquotation {
                            message: format!("Unbound splice variable: {}", var_name.value),
                            range: node.range,
                        });
                    }
                }
            }

            // Recursively substitute in children, handling splices specially
            let mut new_children = Vec::with_capacity(node.children.len());
            for child in &node.children {
                let substituted = substitute_template(child, bindings)?;

                // If this child was a splice and resulted in an App node, expand its children
                if let Syntax::Node(child_node) = child {
                    if child_node.kind == SyntaxKind::SyntaxSplice {
                        // This was a splice - expand its result
                        match &substituted {
                            Syntax::Node(result_node) if result_node.kind == SyntaxKind::App => {
                                // Splice the children of the App node
                                new_children.extend(result_node.children.iter().cloned());
                            }
                            Syntax::Missing => {
                                // Empty splice - don't add anything
                            }
                            _ => {
                                // Single element splice
                                new_children.push(substituted);
                            }
                        }
                    } else {
                        new_children.push(substituted);
                    }
                } else {
                    new_children.push(substituted);
                }
            }

            Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
                kind: node.kind,
                range: node.range,
                children: new_children.into(),
            })))
        }
    }
}
