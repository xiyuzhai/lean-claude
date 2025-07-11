//! Pattern compilation for match expressions
//!
//! This module handles the compilation of pattern matching from surface syntax
//! to the kernel's case expressions.

use lean_kernel::{Expr, Name};
use lean_syn_expr::{Syntax, SyntaxKind};

use crate::{error::ElabError, ElabState};

/// Pattern representation during compilation
#[derive(Debug, Clone)]
pub enum Pattern {
    /// Variable pattern: binds a value
    Var(Name),
    /// Constructor pattern: C p1 ... pn
    Constructor { name: Name, params: Vec<Pattern> },
    /// Literal pattern: numbers, strings, chars
    Literal(Literal),
    /// Wildcard pattern: _
    Wildcard,
    /// As pattern: p@x (binds x to the whole value matched by p)
    As { pattern: Box<Pattern>, name: Name },
}

#[derive(Debug, Clone)]
pub enum Literal {
    Nat(u64),
    String(String),
    Char(char),
}

/// A compiled match arm
#[derive(Debug, Clone)]
pub struct CompiledArm {
    /// Patterns to match (one per discriminant)
    pub patterns: Vec<Pattern>,
    /// Expression to evaluate if patterns match
    pub body: Expr,
    /// Variables bound by the patterns
    pub bound_vars: Vec<Name>,
}

/// Compile a pattern from syntax
pub fn compile_pattern(syntax: &Syntax) -> Result<Pattern, ElabError> {
    match syntax {
        Syntax::Missing => Err(ElabError::MissingSyntax),
        Syntax::Atom(atom) => {
            let s = atom.value.as_str();

            // Check for wildcard
            if s == "_" {
                return Ok(Pattern::Wildcard);
            }

            // Check for literals
            if let Ok(n) = s.parse::<u64>() {
                return Ok(Pattern::Literal(Literal::Nat(n)));
            }

            if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
                let content = &s[1..s.len() - 1];
                return Ok(Pattern::Literal(Literal::String(content.to_string())));
            }

            if s.starts_with('\'') && s.ends_with('\'') && s.len() >= 3 {
                let char_content = &s[1..s.len() - 1];
                let ch = parse_char_literal(char_content)?;
                return Ok(Pattern::Literal(Literal::Char(ch)));
            }

            // Otherwise it's a variable pattern
            Ok(Pattern::Var(Name::mk_simple(s)))
        }
        Syntax::Node(node) => compile_pattern_node(node),
    }
}

fn compile_pattern_node(node: &lean_syn_expr::SyntaxNode) -> Result<Pattern, ElabError> {
    match node.kind {
        SyntaxKind::ConstructorPattern => {
            // Constructor pattern: C p1 ... pn
            if node.children.is_empty() {
                return Err(ElabError::InvalidSyntax("Empty constructor pattern".into()));
            }

            // First child is constructor name (or operator for infix patterns)
            let ctor_name = match &node.children[0] {
                Syntax::Atom(atom) => {
                    let name = atom.value.as_str();
                    // Special handling for list patterns
                    if name == "[]" {
                        Name::str(Name::mk_simple("List"), "nil")
                    } else if name == "::" {
                        Name::str(Name::mk_simple("List"), "cons")
                    } else {
                        Name::mk_simple(name)
                    }
                }
                _ => {
                    return Err(ElabError::InvalidSyntax(
                        "Invalid constructor name in pattern".into(),
                    ))
                }
            };

            // Rest are pattern arguments
            let mut params = Vec::new();
            for child in &node.children[1..] {
                params.push(compile_pattern(child)?);
            }

            Ok(Pattern::Constructor {
                name: ctor_name,
                params,
            })
        }
        SyntaxKind::WildcardPattern => Ok(Pattern::Wildcard),
        _ => Err(ElabError::UnsupportedSyntax(node.kind)),
    }
}

fn parse_char_literal(s: &str) -> Result<char, ElabError> {
    match s {
        "\\n" => Ok('\n'),
        "\\t" => Ok('\t'),
        "\\r" => Ok('\r'),
        "\\\\" => Ok('\\'),
        "\\'" => Ok('\''),
        "\\\"" => Ok('"'),
        _ if s.len() == 1 => Ok(s.chars().next().unwrap()),
        _ => Err(ElabError::InvalidSyntax("Invalid character literal".into())),
    }
}

/// Compile match arms from syntax
pub fn compile_match_arms(
    arms: &[Syntax],
    num_discriminants: usize,
) -> Result<Vec<CompiledArm>, ElabError> {
    let mut compiled_arms = Vec::new();

    for arm_syntax in arms {
        match arm_syntax {
            Syntax::Node(node) if node.kind == SyntaxKind::MatchArm => {
                if node.children.len() < 2 {
                    return Err(ElabError::InvalidSyntax(
                        "Match arm requires pattern and body".into(),
                    ));
                }

                // For single discriminant, pattern is first child
                // For multiple discriminants, we'd need to handle comma-separated patterns
                // For now, handle single discriminant case
                if num_discriminants == 1 {
                    let pattern = compile_pattern(&node.children[0])?;
                    let _body_syntax = &node.children[1];

                    // Collect bound variables from pattern
                    let bound_vars = collect_bound_vars(&pattern);

                    compiled_arms.push(CompiledArm {
                        patterns: vec![pattern],
                        body: Expr::mvar(Name::anonymous()), /* Placeholder - will be elaborated
                                                              * later */
                        bound_vars,
                    });
                } else {
                    // TODO: Handle multiple discriminants
                    return Err(ElabError::UnsupportedSyntax(SyntaxKind::Match));
                }
            }
            _ => return Err(ElabError::InvalidSyntax("Expected match arm".into())),
        }
    }

    Ok(compiled_arms)
}

/// Collect all variables bound by a pattern
fn collect_bound_vars(pattern: &Pattern) -> Vec<Name> {
    let mut vars = Vec::new();
    collect_bound_vars_impl(pattern, &mut vars);
    vars
}

fn collect_bound_vars_impl(pattern: &Pattern, vars: &mut Vec<Name>) {
    match pattern {
        Pattern::Var(name) => vars.push(name.clone()),
        Pattern::Constructor { params, .. } => {
            for p in params {
                collect_bound_vars_impl(p, vars);
            }
        }
        Pattern::As { pattern, name } => {
            vars.push(name.clone());
            collect_bound_vars_impl(pattern, vars);
        }
        Pattern::Literal(_) | Pattern::Wildcard => {}
    }
}

/// Check if a pattern is exhaustive for a given type
pub fn check_exhaustiveness(
    _patterns: &[Pattern],
    _expected_type: &Expr,
    _state: &ElabState,
) -> Result<bool, ElabError> {
    // TODO: Implement exhaustiveness checking
    // For now, assume patterns are exhaustive
    Ok(true)
}

/// Compile patterns to case expressions
pub fn patterns_to_case_expr(
    discriminants: Vec<Expr>,
    _arms: Vec<CompiledArm>,
    _state: &mut ElabState,
) -> Result<Expr, ElabError> {
    // TODO: This is a simplified implementation
    // Real pattern compilation would generate case expressions with proper indices

    if discriminants.len() != 1 {
        return Err(ElabError::UnsupportedSyntax(SyntaxKind::Match));
    }

    // For now, return a placeholder
    // In a real implementation, this would generate:
    // - Case expressions for inductive types
    // - If-then-else chains for literals
    // - Let bindings for variable patterns

    // For now, return a placeholder metavariable
    // In a real implementation, this would generate proper case expressions
    Ok(Expr::mvar(Name::mk_simple("_match_result")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_var_pattern() {
        let pattern = compile_pattern(&Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range: lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
            value: eterned::BaseCoword::new("x"),
        }))
        .unwrap();

        match pattern {
            Pattern::Var(name) => assert_eq!(name.to_string(), "x"),
            _ => panic!("Expected variable pattern"),
        }
    }

    #[test]
    fn test_compile_wildcard_pattern() {
        let pattern = compile_pattern(&Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range: lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
            value: eterned::BaseCoword::new("_"),
        }))
        .unwrap();

        matches!(pattern, Pattern::Wildcard);
    }

    #[test]
    fn test_compile_literal_pattern() {
        // Number literal
        let pattern = compile_pattern(&Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range: lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
            value: eterned::BaseCoword::new("42"),
        }))
        .unwrap();

        match pattern {
            Pattern::Literal(Literal::Nat(n)) => assert_eq!(n, 42),
            _ => panic!("Expected number literal pattern"),
        }
    }
}
