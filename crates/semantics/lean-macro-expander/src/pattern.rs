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

            // Node match - must have same kind and match all children
            (Syntax::Node(p_node), Syntax::Node(s_node)) => {
                if p_node.kind != s_node.kind {
                    return Ok(false);
                }

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

            // Missing matches missing
            (Syntax::Missing, Syntax::Missing) => Ok(true),

            // Otherwise no match
            _ => Ok(false),
        }
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
            // Handle syntax quotations - evaluate their contents
            if node.kind == SyntaxKind::SyntaxQuotation {
                // Evaluate the content of the quotation
                if let Some(content) = node.children.first() {
                    return substitute_template(content, bindings);
                } else {
                    return Err(ExpansionError::InvalidAntiquotation {
                        message: "Empty syntax quotation".to_string(),
                        range: node.range,
                    });
                }
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

            // Recursively substitute in children
            let mut new_children = Vec::with_capacity(node.children.len());
            for child in &node.children {
                new_children.push(substitute_template(child, bindings)?);
            }

            Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
                kind: node.kind,
                range: node.range,
                children: new_children.into(),
            })))
        }
    }
}
