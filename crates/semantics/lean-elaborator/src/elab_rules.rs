//! Custom elaboration rules (elab_rules) infrastructure
//!
//! This module implements support for custom elaboration rules that allow
//! users to extend the elaboration behavior for specific syntax patterns.

use std::collections::HashMap;

use lean_kernel::Name;
use lean_syn_expr::{Syntax, SyntaxAtom, SyntaxKind, SyntaxNode};

use crate::{error::ElabError, ElabState};

/// A single elaboration rule
#[derive(Debug, Clone, PartialEq)]
pub struct ElabRule {
    /// Pattern to match against (using quotation syntax)
    pub pattern: Syntax,
    /// Elaboration function or syntax template
    pub elaborator: ElabRuleAction,
    /// Priority for rule matching (higher priority rules are tried first)
    pub priority: i32,
}

/// The action to take when an elaboration rule matches
#[derive(Debug, Clone, PartialEq)]
pub enum ElabRuleAction {
    /// A syntax template to instantiate
    SyntaxTemplate(Syntax),
    /// A custom elaboration function
    /// In a real implementation, this would be a Lean function reference
    CustomElaborator(Name),
}

/// Registry for custom elaboration rules
#[derive(Debug, Clone)]
pub struct ElabRulesRegistry {
    /// Rules organized by category (term, tactic, command)
    rules_by_category: HashMap<String, Vec<ElabRule>>,
    /// Rules organized by syntax kind for faster lookup
    rules_by_kind: HashMap<SyntaxKind, Vec<ElabRule>>,
}

impl ElabRulesRegistry {
    pub fn new() -> Self {
        Self {
            rules_by_category: HashMap::new(),
            rules_by_kind: HashMap::new(),
        }
    }

    /// Register a new elaboration rule
    pub fn register_rule(&mut self, category: &str, rule: ElabRule) {
        // Add to category map
        self.rules_by_category
            .entry(category.to_string())
            .or_default()
            .push(rule.clone());

        // Extract syntax kind from pattern for faster lookup
        if let Some(kind) = get_pattern_syntax_kind(&rule.pattern) {
            self.rules_by_kind.entry(kind).or_default().push(rule);
        }
    }

    /// Find applicable rules for a given syntax node in a category
    pub fn find_rules(&self, syntax: &Syntax, category: &str) -> Vec<&ElabRule> {
        let mut applicable_rules = Vec::new();

        // First try rules indexed by syntax kind
        if let Some(kind) = syntax.kind() {
            if let Some(rules) = self.rules_by_kind.get(&kind) {
                for rule in rules {
                    if matches_pattern(&rule.pattern, syntax) {
                        applicable_rules.push(rule);
                    }
                }
            }
        }

        // Also check category-specific rules
        if let Some(rules) = self.rules_by_category.get(category) {
            for rule in rules {
                if matches_pattern(&rule.pattern, syntax) && !applicable_rules.contains(&rule) {
                    applicable_rules.push(rule);
                }
            }
        }

        // Sort by priority (descending)
        applicable_rules.sort_by_key(|r| -r.priority);

        applicable_rules
    }

    /// Apply the first matching rule to elaborate the syntax
    /// Returns the instantiated syntax template if a rule matches
    pub fn apply_rules(
        &self,
        syntax: &Syntax,
        category: &str,
    ) -> Result<Option<Syntax>, ElabError> {
        let rules = self.find_rules(syntax, category);

        // Try each rule in priority order until one succeeds
        #[allow(clippy::never_loop)]
        for rule in rules {
            match &rule.elaborator {
                ElabRuleAction::SyntaxTemplate(template) => {
                    // Instantiate the template with bindings from pattern matching
                    let bindings = extract_pattern_bindings(&rule.pattern, syntax)?;
                    let instantiated = instantiate_template(template, &bindings)?;

                    // Return the instantiated syntax for elaboration
                    return Ok(Some(instantiated));
                }
                ElabRuleAction::CustomElaborator(name) => {
                    // In a real implementation, we would call the custom elaborator function
                    // For now, just return an error
                    return Err(ElabError::UnsupportedFeature(format!(
                        "Custom elaborator '{name}' not implemented"
                    )));
                }
            }
        }

        // No matching rules found
        Ok(None)
    }
}

impl Default for ElabRulesRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Apply elab rules to a syntax node
/// This is the main entry point for the elaborator
pub fn apply_elab_rules(
    syntax: &Syntax,
    category: &str,
    state: &ElabState,
) -> Result<Option<Syntax>, ElabError> {
    state.elab_rules.apply_rules(syntax, category)
}

/// Extract the main syntax kind from a pattern
fn get_pattern_syntax_kind(pattern: &Syntax) -> Option<SyntaxKind> {
    match pattern {
        Syntax::Node(node) => {
            // For quotation patterns, look inside the quotation
            if node.kind == SyntaxKind::SyntaxQuotation && !node.children.is_empty() {
                // Look at what's inside the quotation
                match &node.children[0] {
                    Syntax::Node(inner) => Some(inner.kind),
                    _ => None, // Atoms don't have a syntax kind we can index by
                }
            } else {
                Some(node.kind)
            }
        }
        _ => None,
    }
}

/// Check if a syntax node matches a pattern
fn matches_pattern(pattern: &Syntax, syntax: &Syntax) -> bool {
    match (pattern, syntax) {
        (Syntax::Node(pat_node), _) => {
            // Handle quotation patterns
            if pat_node.kind == SyntaxKind::SyntaxQuotation {
                // Extract the pattern inside the quotation
                if let Some(inner_pattern) = pat_node.children.first() {
                    return matches_pattern(inner_pattern, syntax);
                }
            }

            // Handle antiquotations (variables like $x)
            if pat_node.kind == SyntaxKind::SyntaxAntiquotation {
                // Antiquotation matches any syntax
                return true;
            }

            // Otherwise, syntax must be a node with matching kind
            match syntax {
                Syntax::Node(syn_node) => {
                    // Check if kinds match
                    if pat_node.kind != syn_node.kind {
                        return false;
                    }

                    // Check children count (simplified)
                    if pat_node.children.len() != syn_node.children.len() {
                        return false;
                    }

                    // Recursively match children
                    for (pat_child, syn_child) in pat_node.children.iter().zip(&syn_node.children) {
                        if !matches_pattern(pat_child, syn_child) {
                            return false;
                        }
                    }

                    true
                }
                _ => false,
            }
        }
        (Syntax::Atom(pat_atom), Syntax::Atom(syn_atom)) => {
            // Check for antiquotation (pattern variable)
            if pat_atom.value.as_str().starts_with('$') {
                // This is a pattern variable, it matches anything
                true
            } else {
                // Literal match
                pat_atom.value == syn_atom.value
            }
        }
        (Syntax::Atom(pat_atom), _) => {
            // Check if it's a variable pattern
            pat_atom.value.as_str().starts_with('$')
        }
        _ => false,
    }
}

/// Extract bindings from pattern matching
fn extract_pattern_bindings(
    pattern: &Syntax,
    syntax: &Syntax,
) -> Result<HashMap<String, Syntax>, ElabError> {
    let mut bindings = HashMap::new();
    extract_bindings_recursive(pattern, syntax, &mut bindings)?;
    Ok(bindings)
}

fn extract_bindings_recursive(
    pattern: &Syntax,
    syntax: &Syntax,
    bindings: &mut HashMap<String, Syntax>,
) -> Result<(), ElabError> {
    match (pattern, syntax) {
        (Syntax::Node(pat_node), Syntax::Node(syn_node)) => {
            // Handle quotation patterns
            if pat_node.kind == SyntaxKind::SyntaxQuotation {
                if let Some(inner_pattern) = pat_node.children.first() {
                    return extract_bindings_recursive(inner_pattern, syntax, bindings);
                }
            }

            // Handle antiquotations
            if pat_node.kind == SyntaxKind::SyntaxAntiquotation {
                // Extract variable name
                if let Some(Syntax::Atom(atom)) = pat_node.children.first() {
                    let var_name = atom.value.as_str();
                    if let Some(stripped) = var_name.strip_prefix('$') {
                        bindings.insert(stripped.to_string(), syntax.clone());
                    } else {
                        bindings.insert(var_name.to_string(), syntax.clone());
                    }
                }
                return Ok(());
            }

            // Recursively process children
            for (pat_child, syn_child) in pat_node.children.iter().zip(&syn_node.children) {
                extract_bindings_recursive(pat_child, syn_child, bindings)?;
            }
        }
        (Syntax::Atom(pat_atom), syntax) => {
            // Check for pattern variable
            let pat_str = pat_atom.value.as_str();
            if let Some(stripped) = pat_str.strip_prefix('$') {
                bindings.insert(stripped.to_string(), syntax.clone());
            }
        }
        _ => {}
    }

    Ok(())
}

/// Instantiate a template with bindings
fn instantiate_template(
    template: &Syntax,
    bindings: &HashMap<String, Syntax>,
) -> Result<Syntax, ElabError> {
    match template {
        Syntax::Node(node) => {
            // Handle quotations - unwrap them
            if node.kind == SyntaxKind::SyntaxQuotation && node.children.len() == 1 {
                // Unwrap the quotation and instantiate what's inside
                return instantiate_template(&node.children[0], bindings);
            }

            // Handle antiquotations in template
            if node.kind == SyntaxKind::SyntaxAntiquotation {
                if let Some(Syntax::Atom(atom)) = node.children.first() {
                    let var_name = atom.value.as_str();
                    let key = var_name.strip_prefix('$').unwrap_or(var_name);

                    if let Some(value) = bindings.get(key) {
                        return Ok(value.clone());
                    } else {
                        return Err(ElabError::InvalidSyntax(format!(
                            "Unbound pattern variable: {var_name}"
                        )));
                    }
                }
            }

            // Recursively instantiate children
            let mut new_children = Vec::new();
            for child in &node.children {
                new_children.push(instantiate_template(child, bindings)?);
            }

            Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode::new(
                node.kind,
                node.range,
                new_children.into(),
            ))))
        }
        Syntax::Atom(_) => Ok(template.clone()),
        Syntax::Missing => Ok(template.clone()),
    }
}

#[cfg(test)]
mod tests {
    use lean_syn_expr::{SourcePos, SourceRange, SyntaxAtom, SyntaxNode};

    use super::*;

    fn dummy_range() -> SourceRange {
        SourceRange {
            start: SourcePos::new(0, 0, 0),
            end: SourcePos::new(0, 0, 0),
        }
    }

    #[test]
    fn test_pattern_matching_literal() {
        // Pattern: `(myterm)`
        let pattern = Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::SyntaxQuotation,
            dummy_range(),
            vec![Syntax::Atom(SyntaxAtom::new(
                dummy_range(),
                eterned::BaseCoword::new("myterm"),
            ))]
            .into(),
        )));

        // Syntax to match: myterm
        let syntax = Syntax::Atom(SyntaxAtom::new(
            dummy_range(),
            eterned::BaseCoword::new("myterm"),
        ));

        assert!(matches_pattern(&pattern, &syntax));

        // Non-matching syntax: other
        let non_match = Syntax::Atom(SyntaxAtom::new(
            dummy_range(),
            eterned::BaseCoword::new("other"),
        ));

        assert!(!matches_pattern(&pattern, &non_match));
    }

    #[test]
    fn test_pattern_matching_variable() {
        // Pattern: `($x)`
        let pattern = Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::SyntaxQuotation,
            dummy_range(),
            vec![Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::SyntaxAntiquotation,
                dummy_range(),
                vec![Syntax::Atom(SyntaxAtom::new(
                    dummy_range(),
                    eterned::BaseCoword::new("$x"),
                ))]
                .into(),
            )))]
            .into(),
        )));

        // Any syntax should match
        let syntax1 = Syntax::Atom(SyntaxAtom::new(
            dummy_range(),
            eterned::BaseCoword::new("anything"),
        ));

        let syntax2 = Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::App,
            dummy_range(),
            vec![].into(),
        )));

        assert!(matches_pattern(&pattern, &syntax1));
        assert!(matches_pattern(&pattern, &syntax2));
    }

    #[test]
    fn test_extract_bindings() {
        // Pattern: `(f $x $y)`
        let pattern = Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::SyntaxQuotation,
            dummy_range(),
            vec![Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::App,
                dummy_range(),
                vec![
                    Syntax::Atom(SyntaxAtom::new(
                        dummy_range(),
                        eterned::BaseCoword::new("f"),
                    )),
                    Syntax::Atom(SyntaxAtom::new(
                        dummy_range(),
                        eterned::BaseCoword::new("$x"),
                    )),
                    Syntax::Atom(SyntaxAtom::new(
                        dummy_range(),
                        eterned::BaseCoword::new("$y"),
                    )),
                ]
                .into(),
            )))]
            .into(),
        )));

        // Syntax: (f a b)
        let syntax = Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::App,
            dummy_range(),
            vec![
                Syntax::Atom(SyntaxAtom::new(
                    dummy_range(),
                    eterned::BaseCoword::new("f"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    dummy_range(),
                    eterned::BaseCoword::new("a"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    dummy_range(),
                    eterned::BaseCoword::new("b"),
                )),
            ]
            .into(),
        )));

        let bindings = extract_pattern_bindings(&pattern, &syntax).unwrap();
        assert_eq!(bindings.len(), 2);

        match bindings.get("x") {
            Some(Syntax::Atom(atom)) => assert_eq!(atom.value.as_str(), "a"),
            _ => panic!("Expected binding for x"),
        }

        match bindings.get("y") {
            Some(Syntax::Atom(atom)) => assert_eq!(atom.value.as_str(), "b"),
            _ => panic!("Expected binding for y"),
        }
    }

    #[test]
    fn test_registry_basic() {
        let mut registry = ElabRulesRegistry::new();

        // Register a simple rule: `(myterm) => `(42)
        let pattern = Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::SyntaxQuotation,
            dummy_range(),
            vec![Syntax::Atom(SyntaxAtom::new(
                dummy_range(),
                eterned::BaseCoword::new("myterm"),
            ))]
            .into(),
        )));

        let template = Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::SyntaxQuotation,
            dummy_range(),
            vec![Syntax::Atom(SyntaxAtom::new(
                dummy_range(),
                eterned::BaseCoword::new("42"),
            ))]
            .into(),
        )));

        let rule = ElabRule {
            pattern,
            elaborator: ElabRuleAction::SyntaxTemplate(template),
            priority: 100,
        };

        registry.register_rule("term", rule);

        // Test finding rules
        let test_syntax = Syntax::Atom(SyntaxAtom::new(
            dummy_range(),
            eterned::BaseCoword::new("myterm"),
        ));

        let found_rules = registry.find_rules(&test_syntax, "term");
        assert_eq!(found_rules.len(), 1);

        // Test applying rules
        let result = registry.apply_rules(&test_syntax, "term");
        assert!(result.is_ok());
        assert!(result.unwrap().is_some());
    }
}
