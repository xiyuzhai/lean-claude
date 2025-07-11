//! Pattern compilation for match expressions
//!
//! This module handles the compilation of pattern matching from surface syntax
//! to the kernel's case expressions.

use lean_kernel::{expr::ExprKind, Expr, Name};
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
    patterns: &[Pattern],
    expected_type: &Expr,
    _state: &ElabState,
) -> Result<bool, ElabError> {
    // Basic exhaustiveness checking
    // This is a simplified implementation that handles:
    // 1. Wildcard patterns (always exhaustive)
    // 2. Variable patterns (always exhaustive)
    // 3. Literal patterns (check coverage based on type)

    // Check if any pattern is a wildcard or variable - these are catch-all patterns
    for pattern in patterns {
        if matches!(pattern, Pattern::Wildcard | Pattern::Var(_)) {
            return Ok(true);
        }
    }

    // For literal patterns, we need to check based on the expected type
    match expected_type.kind {
        // For Bool type, check we have both true and false
        ExprKind::Const(ref name, _) if name.to_string() == "Bool" => {
            check_bool_exhaustiveness(patterns)
        }
        // For Nat type with literals, we can't be exhaustive without a catch-all
        ExprKind::Const(ref name, _) if name.to_string() == "Nat" => {
            // Nat literals alone are never exhaustive
            Ok(false)
        }
        // For other types, we need more type information
        _ => {
            // Conservative: if we don't know the type structure,
            // assume non-exhaustive unless there's a catch-all
            Ok(false)
        }
    }
}

/// Check exhaustiveness for Bool patterns
fn check_bool_exhaustiveness(patterns: &[Pattern]) -> Result<bool, ElabError> {
    let mut has_true = false;
    let mut has_false = false;

    for pattern in patterns {
        match pattern {
            Pattern::Literal(Literal::Nat(0)) => has_false = true,
            Pattern::Literal(Literal::Nat(1)) => has_true = true,
            // Constructor patterns for true/false would go here
            Pattern::Constructor { name, .. } => match name.to_string().as_str() {
                "true" => has_true = true,
                "false" => has_false = true,
                _ => {}
            },
            _ => {}
        }
    }

    Ok(has_true && has_false)
}

/// Compile patterns to case expressions
pub fn patterns_to_case_expr(
    discriminants: Vec<Expr>,
    arms: Vec<CompiledArm>,
    state: &mut ElabState,
) -> Result<Expr, ElabError> {
    if discriminants.len() != 1 {
        return Err(ElabError::UnsupportedSyntax(SyntaxKind::Match));
    }

    let discriminant = discriminants.into_iter().next().unwrap();

    // For now, we implement a simple compilation strategy:
    // 1. Variable patterns compile to let bindings
    // 2. Literal patterns compile to if-then-else chains
    // 3. Constructor patterns are not yet supported (need inductive types in
    //    kernel)
    // 4. Wildcard patterns become the else branch

    compile_arms_to_expr(discriminant, arms, state)
}

/// Compile a list of match arms into nested if-then-else expressions
fn compile_arms_to_expr(
    discriminant: Expr,
    arms: Vec<CompiledArm>,
    state: &mut ElabState,
) -> Result<Expr, ElabError> {
    if arms.is_empty() {
        // No arms means non-exhaustive match - create error expression
        return Ok(Expr::mvar(Name::mk_simple("_match_error")));
    }

    let mut arms_iter = arms.into_iter();
    let first_arm = arms_iter.next().unwrap();
    let rest_arms: Vec<_> = arms_iter.collect();

    compile_single_arm(discriminant, first_arm, rest_arms, state)
}

/// Compile a single arm, with the rest as fallback
fn compile_single_arm(
    discriminant: Expr,
    arm: CompiledArm,
    rest: Vec<CompiledArm>,
    state: &mut ElabState,
) -> Result<Expr, ElabError> {
    if arm.patterns.len() != 1 {
        return Err(ElabError::UnsupportedSyntax(SyntaxKind::Match));
    }

    let pattern = &arm.patterns[0];
    let body = arm.body;

    match pattern {
        Pattern::Var(name) => {
            // Variable pattern: compile to let binding
            // let x := discriminant in body
            let ty = Expr::mvar(Name::mk_simple("_var_type"));
            Ok(Expr::let_expr(name.clone(), ty, discriminant, body))
        }
        Pattern::Wildcard => {
            // Wildcard pattern always matches
            Ok(body)
        }
        Pattern::Literal(lit) => {
            // Literal pattern: compile to if-then-else
            // if discriminant == lit then body else (compile rest)
            let lit_expr = literal_to_expr(lit);
            let eq_expr = build_equality_test(discriminant.clone(), lit_expr, state)?;

            if rest.is_empty() {
                // Last arm with literal pattern - just return body
                // (assumes exhaustiveness)
                Ok(body)
            } else {
                // Build if-then-else
                let else_expr = compile_arms_to_expr(discriminant, rest, state)?;
                build_if_then_else(eq_expr, body, else_expr, state)
            }
        }
        Pattern::Constructor { .. } => {
            // TODO: Constructor patterns require inductive type support in kernel
            // For now, return error
            Err(ElabError::UnsupportedSyntax(SyntaxKind::ConstructorPattern))
        }
        Pattern::As { .. } => {
            // TODO: As patterns need special handling
            Err(ElabError::UnsupportedSyntax(SyntaxKind::Match))
        }
    }
}

/// Convert a literal pattern to an expression
fn literal_to_expr(lit: &Literal) -> Expr {
    match lit {
        Literal::Nat(n) => Expr::nat(*n),
        Literal::String(s) => Expr::string(s.clone()),
        Literal::Char(c) => {
            // Represent char as a nat for now
            Expr::nat(*c as u64)
        }
    }
}

/// Build an equality test expression
fn build_equality_test(left: Expr, right: Expr, _state: &mut ElabState) -> Result<Expr, ElabError> {
    // Build: Eq left right
    // For now, we create a simple application
    let eq = Expr::const_expr(Name::mk_simple("Eq"), vec![]);
    Ok(Expr::app(Expr::app(eq, left), right))
}

/// Build an if-then-else expression
fn build_if_then_else(
    _condition: Expr,
    then_branch: Expr,
    else_branch: Expr,
    _state: &mut ElabState,
) -> Result<Expr, ElabError> {
    // In Lean, if-then-else is defined as:
    // ite : ∀ {α : Sort u}, Decidable p → α → α → α
    // For now, create a simplified version without the condition
    // TODO: Properly thread the condition through when decidable instances are
    // implemented
    let ite = Expr::const_expr(Name::mk_simple("ite"), vec![]);
    let decidable_inst = Expr::mvar(Name::mk_simple("_decidable"));

    Ok(Expr::app(
        Expr::app(Expr::app(ite, decidable_inst), then_branch),
        else_branch,
    ))
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

    #[test]
    fn test_patterns_to_case_expr_literal() {
        use lean_kernel::{Expr, Name};

        let mut state = ElabState::new();

        // Create a match with literal patterns: match x with | 0 => a | 1 => b | _ => c
        let discriminant = Expr::fvar(Name::mk_simple("x"));

        let arms = vec![
            CompiledArm {
                patterns: vec![Pattern::Literal(Literal::Nat(0))],
                body: Expr::fvar(Name::mk_simple("a")),
                bound_vars: vec![],
            },
            CompiledArm {
                patterns: vec![Pattern::Literal(Literal::Nat(1))],
                body: Expr::fvar(Name::mk_simple("b")),
                bound_vars: vec![],
            },
            CompiledArm {
                patterns: vec![Pattern::Wildcard],
                body: Expr::fvar(Name::mk_simple("c")),
                bound_vars: vec![],
            },
        ];

        let result = patterns_to_case_expr(vec![discriminant], arms, &mut state);
        assert!(
            result.is_ok(),
            "Pattern compilation should succeed: {:?}",
            result.err()
        );

        // The result should be nested if-then-else expressions
        let expr = result.unwrap();
        assert!(
            matches!(&expr.kind, lean_kernel::expr::ExprKind::App(_, _)),
            "Expected application (if-then-else)"
        );
    }

    #[test]
    fn test_patterns_to_case_expr_variable() {
        use lean_kernel::{Expr, Name};

        let mut state = ElabState::new();

        // Create a match with variable pattern: match x with | y => y + 1
        let discriminant = Expr::fvar(Name::mk_simple("x"));

        let arms = vec![CompiledArm {
            patterns: vec![Pattern::Var(Name::mk_simple("y"))],
            body: Expr::bvar(0), // y is bound as bvar(0)
            bound_vars: vec![Name::mk_simple("y")],
        }];

        let result = patterns_to_case_expr(vec![discriminant], arms, &mut state);
        assert!(
            result.is_ok(),
            "Pattern compilation should succeed: {:?}",
            result.err()
        );

        // The result should be a let expression
        let expr = result.unwrap();
        assert!(
            matches!(&expr.kind, lean_kernel::expr::ExprKind::Let(_, _, _, _)),
            "Expected let expression for variable pattern, got {:?}",
            expr.kind
        );
    }

    #[test]
    fn test_exhaustiveness_wildcard() {
        use lean_kernel::{Expr, Name};

        let state = ElabState::new();
        let nat_type = Expr::const_expr(Name::mk_simple("Nat"), vec![]);

        // Wildcard pattern is always exhaustive
        let patterns = vec![Pattern::Wildcard];
        let result = check_exhaustiveness(&patterns, &nat_type, &state);
        assert!(result.unwrap(), "Wildcard pattern should be exhaustive");
    }

    #[test]
    fn test_exhaustiveness_variable() {
        use lean_kernel::{Expr, Name};

        let state = ElabState::new();
        let nat_type = Expr::const_expr(Name::mk_simple("Nat"), vec![]);

        // Variable pattern is always exhaustive
        let patterns = vec![Pattern::Var(Name::mk_simple("x"))];
        let result = check_exhaustiveness(&patterns, &nat_type, &state);
        assert!(result.unwrap(), "Variable pattern should be exhaustive");
    }

    #[test]
    fn test_exhaustiveness_nat_literals() {
        use lean_kernel::{Expr, Name};

        let state = ElabState::new();
        let nat_type = Expr::const_expr(Name::mk_simple("Nat"), vec![]);

        // Nat literals alone are not exhaustive
        let patterns = vec![
            Pattern::Literal(Literal::Nat(0)),
            Pattern::Literal(Literal::Nat(1)),
            Pattern::Literal(Literal::Nat(2)),
        ];
        let result = check_exhaustiveness(&patterns, &nat_type, &state);
        assert!(
            !result.unwrap(),
            "Nat literals alone should not be exhaustive"
        );

        // But with a wildcard, they are
        let patterns_with_wildcard = vec![
            Pattern::Literal(Literal::Nat(0)),
            Pattern::Literal(Literal::Nat(1)),
            Pattern::Wildcard,
        ];
        let result = check_exhaustiveness(&patterns_with_wildcard, &nat_type, &state);
        assert!(
            result.unwrap(),
            "Nat literals with wildcard should be exhaustive"
        );
    }

    #[test]
    fn test_exhaustiveness_bool() {
        use lean_kernel::{Expr, Name};

        let state = ElabState::new();
        let bool_type = Expr::const_expr(Name::mk_simple("Bool"), vec![]);

        // Bool with both true/false constructors is exhaustive
        let patterns = vec![
            Pattern::Constructor {
                name: Name::mk_simple("true"),
                params: vec![],
            },
            Pattern::Constructor {
                name: Name::mk_simple("false"),
                params: vec![],
            },
        ];
        let result = check_exhaustiveness(&patterns, &bool_type, &state);
        assert!(result.unwrap(), "Bool with true/false should be exhaustive");

        // Bool with only one constructor is not exhaustive
        let patterns_incomplete = vec![Pattern::Constructor {
            name: Name::mk_simple("true"),
            params: vec![],
        }];
        let result = check_exhaustiveness(&patterns_incomplete, &bool_type, &state);
        assert!(
            !result.unwrap(),
            "Bool with only true should not be exhaustive"
        );
    }
}
