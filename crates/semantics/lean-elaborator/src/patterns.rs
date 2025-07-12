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
    /// Structure pattern: { field1 := p1, field2 := p2, ... }
    Structure {
        name: Name,
        fields: Vec<FieldPattern>,
    },
    /// Tuple pattern: (p1, p2, ..., pn)
    Tuple { patterns: Vec<Pattern> },
    /// Literal pattern: numbers, strings, chars
    Literal(Literal),
    /// Wildcard pattern: _
    Wildcard,
    /// As pattern: p@x (binds x to the whole value matched by p)
    As { pattern: Box<Pattern>, name: Name },
    /// Guarded pattern: pattern if condition
    Guarded {
        pattern: Box<Pattern>,
        guard: GuardCondition,
    },
}

/// Guard condition in pattern matching
#[derive(Debug, Clone)]
pub enum GuardCondition {
    /// Simple boolean expression
    BoolExpr(Expr),
    /// Equality check: expr == value
    Equals { expr: Expr, value: Expr },
    /// Comparison: expr < value, expr > value, etc.
    Compare {
        op: ComparisonOp,
        left: Expr,
        right: Expr,
    },
}

/// Comparison operators for guards
#[derive(Debug, Clone)]
pub enum ComparisonOp {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
}

/// Field pattern in structure patterns
#[derive(Debug, Clone)]
pub struct FieldPattern {
    /// Field name
    pub name: Name,
    /// Pattern for the field value
    pub pattern: Pattern,
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
        SyntaxKind::StructurePattern => {
            // Structure pattern: { field1 := p1, field2 := p2, ... }
            compile_structure_pattern(node)
        }
        SyntaxKind::TuplePattern => {
            // Tuple pattern: (p1, p2, ..., pn)
            compile_tuple_pattern(node)
        }
        SyntaxKind::WildcardPattern => Ok(Pattern::Wildcard),
        _ => Err(ElabError::UnsupportedSyntax(node.kind)),
    }
}

/// Compile a structure pattern from syntax
/// Expected syntax: { field1 := pattern1, field2 := pattern2, ... }
fn compile_structure_pattern(node: &lean_syn_expr::SyntaxNode) -> Result<Pattern, ElabError> {
    if node.children.is_empty() {
        return Err(ElabError::InvalidSyntax("Empty structure pattern".into()));
    }

    // The first child should be the structure name (optional)
    // If it starts with a brace, it's an anonymous structure pattern
    let (start_idx, struct_name) = if !node.children.is_empty() {
        match &node.children[0] {
            Syntax::Atom(atom) if atom.value.as_str() == "{" => {
                // Anonymous structure pattern: { field1 := p1, ... }
                (1, Name::anonymous())
            }
            Syntax::Atom(atom) => {
                // Named structure pattern: StructName { field1 := p1, ... }
                (1, Name::mk_simple(atom.value.as_str()))
            }
            _ => {
                // Assume anonymous if first child is not an atom
                (0, Name::anonymous())
            }
        }
    } else {
        return Err(ElabError::InvalidSyntax("Empty structure pattern".into()));
    };

    let mut fields = Vec::new();
    let mut i = start_idx;

    // Skip opening brace if present
    if i < node.children.len() {
        if let Syntax::Atom(atom) = &node.children[i] {
            if atom.value.as_str() == "{" {
                i += 1;
            }
        }
    }

    // Parse field patterns
    while i < node.children.len() {
        // Skip closing brace
        if let Syntax::Atom(atom) = &node.children[i] {
            if atom.value.as_str() == "}" {
                break;
            }
        }

        // Parse field assignment: field_name := pattern
        if i + 2 < node.children.len() {
            let field_name = match &node.children[i] {
                Syntax::Atom(atom) => Name::mk_simple(atom.value.as_str()),
                _ => {
                    return Err(ElabError::InvalidSyntax(
                        "Expected field name in structure pattern".into(),
                    ))
                }
            };

            // Skip := operator
            i += 1;
            if let Syntax::Atom(atom) = &node.children[i] {
                if atom.value.as_str() != ":=" {
                    return Err(ElabError::InvalidSyntax(
                        "Expected ':=' in structure pattern field".into(),
                    ));
                }
            }
            i += 1;

            // Parse field pattern
            let field_pattern = compile_pattern(&node.children[i])?;
            fields.push(FieldPattern {
                name: field_name,
                pattern: field_pattern,
            });
            i += 1;

            // Skip comma if present
            if i < node.children.len() {
                if let Syntax::Atom(atom) = &node.children[i] {
                    if atom.value.as_str() == "," {
                        i += 1;
                    }
                }
            }
        } else {
            break;
        }
    }

    Ok(Pattern::Structure {
        name: struct_name,
        fields,
    })
}

/// Compile a tuple pattern from syntax
/// Expected syntax: (p1, p2, ..., pn)
fn compile_tuple_pattern(node: &lean_syn_expr::SyntaxNode) -> Result<Pattern, ElabError> {
    if node.children.is_empty() {
        return Ok(Pattern::Tuple {
            patterns: Vec::new(),
        });
    }

    let mut patterns = Vec::new();
    let mut i = 0;

    // Skip opening parenthesis if present
    if i < node.children.len() {
        if let Syntax::Atom(atom) = &node.children[i] {
            if atom.value.as_str() == "(" {
                i += 1;
            }
        }
    }

    // Parse patterns separated by commas
    while i < node.children.len() {
        // Skip closing parenthesis
        if let Syntax::Atom(atom) = &node.children[i] {
            if atom.value.as_str() == ")" {
                break;
            }
        }

        // Skip commas
        if let Syntax::Atom(atom) = &node.children[i] {
            if atom.value.as_str() == "," {
                i += 1;
                continue;
            }
        }

        // Parse pattern
        let pattern = compile_pattern(&node.children[i])?;
        patterns.push(pattern);
        i += 1;
    }

    Ok(Pattern::Tuple { patterns })
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
        Pattern::Structure { fields, .. } => {
            for field in fields {
                collect_bound_vars_impl(&field.pattern, vars);
            }
        }
        Pattern::Tuple { patterns } => {
            for p in patterns {
                collect_bound_vars_impl(p, vars);
            }
        }
        Pattern::As { pattern, name } => {
            vars.push(name.clone());
            collect_bound_vars_impl(pattern, vars);
        }
        Pattern::Guarded { pattern, .. } => {
            // Guarded patterns bind the same variables as their underlying pattern
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
        Pattern::Structure { fields, .. } => {
            // Structure pattern: compile to field projections and nested matching
            compile_structure_pattern_to_expr(discriminant, fields, body, rest, state)
        }
        Pattern::Tuple { patterns } => {
            // Tuple pattern: compile to tuple projections and nested matching
            compile_tuple_pattern_to_expr(discriminant, patterns, body, rest, state)
        }
        Pattern::Guarded { pattern, guard } => {
            // Guarded pattern: compile pattern first, then add guard condition
            compile_guarded_pattern_to_expr(discriminant, pattern, guard, body, rest, state)
        }
        Pattern::As { .. } => {
            // TODO: As patterns need special handling
            Err(ElabError::UnsupportedSyntax(SyntaxKind::Match))
        }
    }
}

/// Compile a structure pattern to an expression
/// This creates nested let bindings for each field and then evaluates the body
fn compile_structure_pattern_to_expr(
    discriminant: Expr,
    fields: &[FieldPattern],
    body: Expr,
    rest: Vec<CompiledArm>,
    state: &mut ElabState,
) -> Result<Expr, ElabError> {
    if fields.is_empty() {
        // Empty structure pattern just matches the body
        return Ok(body);
    }

    // For each field pattern, create a projection and bind variables
    // Start from the innermost pattern and work outward
    let mut current_body = body;

    // Process fields in reverse order to build nested let expressions
    for field in fields.iter().rev() {
        // Create field projection: discriminant.field_name
        let field_proj = Expr::proj(
            Name::mk_simple("_struct"), // Placeholder struct name
            0,                          // Field index - simplified for now
            discriminant.clone(),
        );

        // Compile the field pattern against the projection
        match &field.pattern {
            Pattern::Var(var_name) => {
                // Simple variable binding: let var_name := discriminant.field_name in body
                let var_type = Expr::mvar(Name::mk_simple("_field_type"));
                current_body = Expr::let_expr(var_name.clone(), var_type, field_proj, current_body);
            }
            Pattern::Wildcard => {
                // Wildcard doesn't bind anything, just continue
                continue;
            }
            Pattern::Literal(lit) => {
                // Field literal pattern: if discriminant.field_name == literal then body else
                // rest
                let lit_expr = literal_to_expr(lit);
                let eq_expr = build_equality_test(field_proj, lit_expr, state)?;

                if rest.is_empty() {
                    current_body = build_if_then_else(
                        eq_expr,
                        current_body,
                        Expr::mvar(Name::mk_simple("_match_error")),
                        state,
                    )?;
                } else {
                    let else_expr =
                        compile_arms_to_expr(discriminant.clone(), rest.clone(), state)?;
                    current_body = build_if_then_else(eq_expr, current_body, else_expr, state)?;
                }
            }
            _ => {
                // Nested patterns (constructor, structure, as) are not yet supported
                return Err(ElabError::UnsupportedSyntax(SyntaxKind::StructurePattern));
            }
        }
    }

    Ok(current_body)
}

/// Compile a tuple pattern to an expression
/// This creates projections for each tuple element and binds variables
fn compile_tuple_pattern_to_expr(
    discriminant: Expr,
    patterns: &[Pattern],
    body: Expr,
    rest: Vec<CompiledArm>,
    state: &mut ElabState,
) -> Result<Expr, ElabError> {
    if patterns.is_empty() {
        // Empty tuple pattern (unit type) just matches the body
        return Ok(body);
    }

    // For each pattern, create a tuple projection and bind variables
    // Start from the innermost pattern and work outward
    let mut current_body = body;

    // Process patterns in reverse order to build nested let expressions
    for (idx, pattern) in patterns.iter().enumerate().rev() {
        // Create tuple projection: discriminant.idx
        let tuple_proj = Expr::proj(
            Name::mk_simple("_tuple"), // Placeholder tuple type name
            idx as u32,                // Element index
            discriminant.clone(),
        );

        // Compile the pattern against the projection
        match pattern {
            Pattern::Var(var_name) => {
                // Simple variable binding: let var_name := discriminant.idx in body
                let var_type = Expr::mvar(Name::mk_simple("_elem_type"));
                current_body = Expr::let_expr(var_name.clone(), var_type, tuple_proj, current_body);
            }
            Pattern::Wildcard => {
                // Wildcard doesn't bind anything, just continue
                continue;
            }
            Pattern::Literal(lit) => {
                // Element literal pattern: if discriminant.idx == literal then body else rest
                let lit_expr = literal_to_expr(lit);
                let eq_expr = build_equality_test(tuple_proj, lit_expr, state)?;

                if rest.is_empty() {
                    current_body = build_if_then_else(
                        eq_expr,
                        current_body,
                        Expr::mvar(Name::mk_simple("_match_error")),
                        state,
                    )?;
                } else {
                    let else_expr =
                        compile_arms_to_expr(discriminant.clone(), rest.clone(), state)?;
                    current_body = build_if_then_else(eq_expr, current_body, else_expr, state)?;
                }
            }
            Pattern::Tuple {
                patterns: nested_patterns,
            } => {
                // Nested tuple pattern: recursively compile
                current_body = compile_tuple_pattern_to_expr(
                    tuple_proj,
                    nested_patterns,
                    current_body,
                    rest.clone(),
                    state,
                )?;
            }
            Pattern::Structure { fields, .. } => {
                // Nested structure pattern: recursively compile
                current_body = compile_structure_pattern_to_expr(
                    tuple_proj,
                    fields,
                    current_body,
                    rest.clone(),
                    state,
                )?;
            }
            _ => {
                // Other nested patterns (constructor, as) are not yet supported
                return Err(ElabError::UnsupportedSyntax(SyntaxKind::TuplePattern));
            }
        }
    }

    Ok(current_body)
}

/// Compile a guarded pattern to an expression
/// This compiles the underlying pattern first, then adds the guard condition
fn compile_guarded_pattern_to_expr(
    discriminant: Expr,
    pattern: &Pattern,
    guard: &GuardCondition,
    body: Expr,
    rest: Vec<CompiledArm>,
    state: &mut ElabState,
) -> Result<Expr, ElabError> {
    // First compile the underlying pattern to create variable bindings
    let pattern_expr = match pattern {
        Pattern::Var(name) => {
            // Variable pattern: let name := discriminant in (guard check)
            let var_type = Expr::mvar(Name::mk_simple("_var_type"));
            let guard_expr = compile_guard_condition(guard, state)?;
            let then_expr = body;
            let else_expr = if rest.is_empty() {
                Expr::mvar(Name::mk_simple("_match_error"))
            } else {
                compile_arms_to_expr(discriminant.clone(), rest, state)?
            };
            let conditional = build_if_then_else(guard_expr, then_expr, else_expr, state)?;
            Expr::let_expr(name.clone(), var_type, discriminant, conditional)
        }
        Pattern::Wildcard => {
            // Wildcard with guard: just check the guard condition
            let guard_expr = compile_guard_condition(guard, state)?;
            let then_expr = body;
            let else_expr = if rest.is_empty() {
                Expr::mvar(Name::mk_simple("_match_error"))
            } else {
                compile_arms_to_expr(discriminant, rest, state)?
            };
            build_if_then_else(guard_expr, then_expr, else_expr, state)?
        }
        Pattern::Literal(lit) => {
            // Literal pattern with guard: check literal match AND guard
            let lit_expr = literal_to_expr(lit);
            let pattern_check = build_equality_test(discriminant.clone(), lit_expr, state)?;
            let guard_expr = compile_guard_condition(guard, state)?;

            // Combine pattern check AND guard check
            let combined_check = build_logical_and(pattern_check, guard_expr, state)?;

            let then_expr = body;
            let else_expr = if rest.is_empty() {
                Expr::mvar(Name::mk_simple("_match_error"))
            } else {
                compile_arms_to_expr(discriminant, rest, state)?
            };
            build_if_then_else(combined_check, then_expr, else_expr, state)?
        }
        _ => {
            // For complex patterns (constructor, structure, tuple), we need to
            // first match the pattern, then check the guard
            // This is a simplified implementation - a full implementation would
            // need to properly integrate guard checking with pattern matching
            return Err(ElabError::UnsupportedFeature(
                "Guards on complex patterns not yet implemented".to_string(),
            ));
        }
    };

    Ok(pattern_expr)
}

/// Compile a guard condition to a boolean expression
fn compile_guard_condition(
    guard: &GuardCondition,
    state: &mut ElabState,
) -> Result<Expr, ElabError> {
    match guard {
        GuardCondition::BoolExpr(expr) => Ok(expr.clone()),
        GuardCondition::Equals { expr, value } => {
            build_equality_test(expr.clone(), value.clone(), state)
        }
        GuardCondition::Compare { op, left, right } => {
            let op_name = match op {
                ComparisonOp::Less => "LT.lt",
                ComparisonOp::LessEqual => "LE.le",
                ComparisonOp::Greater => "GT.gt",
                ComparisonOp::GreaterEqual => "GE.ge",
                ComparisonOp::Equal => "Eq.eq",
                ComparisonOp::NotEqual => "Ne.ne",
            };
            let op_expr = Expr::const_expr(Name::mk_simple(op_name), vec![]);
            Ok(Expr::app(Expr::app(op_expr, left.clone()), right.clone()))
        }
    }
}

/// Build a logical AND expression
fn build_logical_and(left: Expr, right: Expr, _state: &mut ElabState) -> Result<Expr, ElabError> {
    // In Lean, logical AND is typically: left && right
    let and_op = Expr::const_expr(Name::mk_simple("And"), vec![]);
    Ok(Expr::app(Expr::app(and_op, left), right))
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
        let pattern = compile_pattern(&Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
            lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
            eterned::BaseCoword::new("x"),
        )))
        .unwrap();

        match pattern {
            Pattern::Var(name) => assert_eq!(name.to_string(), "x"),
            _ => panic!("Expected variable pattern"),
        }
    }

    #[test]
    fn test_compile_wildcard_pattern() {
        let pattern = compile_pattern(&Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
            lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
            eterned::BaseCoword::new("_"),
        )))
        .unwrap();

        matches!(pattern, Pattern::Wildcard);
    }

    #[test]
    fn test_compile_literal_pattern() {
        // Number literal
        let pattern = compile_pattern(&Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
            lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
            eterned::BaseCoword::new("42"),
        )))
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

    #[test]
    fn test_compile_structure_pattern() {
        use lean_syn_expr::{SourcePos, SourceRange, SyntaxAtom, SyntaxNode};

        // Create a structure pattern: { x := a, y := b }
        let pattern_node = SyntaxNode::new(
            SyntaxKind::StructurePattern,
            SourceRange {
                start: SourcePos::new(0, 0, 0),
                end: SourcePos::new(0, 0, 0),
            },
            vec![
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("{"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("x"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new(":="),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("a"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new(","),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("y"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new(":="),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("b"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("}"),
                )),
            ]
            .into(),
        );

        let pattern = compile_structure_pattern(&pattern_node).unwrap();

        match pattern {
            Pattern::Structure { name: _, fields } => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].name.to_string(), "x");
                assert_eq!(fields[1].name.to_string(), "y");

                match (&fields[0].pattern, &fields[1].pattern) {
                    (Pattern::Var(x_name), Pattern::Var(y_name)) => {
                        assert_eq!(x_name.to_string(), "a");
                        assert_eq!(y_name.to_string(), "b");
                    }
                    _ => panic!("Expected variable patterns for fields"),
                }
            }
            _ => panic!("Expected structure pattern"),
        }
    }

    #[test]
    fn test_structure_pattern_bound_vars() {
        let pattern = Pattern::Structure {
            name: Name::mk_simple("Point"),
            fields: vec![
                FieldPattern {
                    name: Name::mk_simple("x"),
                    pattern: Pattern::Var(Name::mk_simple("x_val")),
                },
                FieldPattern {
                    name: Name::mk_simple("y"),
                    pattern: Pattern::Var(Name::mk_simple("y_val")),
                },
            ],
        };

        let bound_vars = collect_bound_vars(&pattern);
        assert_eq!(bound_vars.len(), 2);
        assert!(bound_vars.contains(&Name::mk_simple("x_val")));
        assert!(bound_vars.contains(&Name::mk_simple("y_val")));
    }

    #[test]
    fn test_compile_tuple_pattern() {
        use lean_syn_expr::{SourcePos, SourceRange, SyntaxAtom, SyntaxNode};

        // Create a tuple pattern: (a, b, c)
        let pattern_node = SyntaxNode::new(
            SyntaxKind::TuplePattern,
            SourceRange {
                start: SourcePos::new(0, 0, 0),
                end: SourcePos::new(0, 0, 0),
            },
            vec![
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("("),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("a"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new(","),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("b"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new(","),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("c"),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new(")"),
                )),
            ]
            .into(),
        );

        let pattern = compile_tuple_pattern(&pattern_node).unwrap();

        match pattern {
            Pattern::Tuple { patterns } => {
                assert_eq!(patterns.len(), 3);
                match (&patterns[0], &patterns[1], &patterns[2]) {
                    (Pattern::Var(a_name), Pattern::Var(b_name), Pattern::Var(c_name)) => {
                        assert_eq!(a_name.to_string(), "a");
                        assert_eq!(b_name.to_string(), "b");
                        assert_eq!(c_name.to_string(), "c");
                    }
                    _ => panic!("Expected variable patterns for tuple elements"),
                }
            }
            _ => panic!("Expected tuple pattern"),
        }
    }

    #[test]
    fn test_tuple_pattern_bound_vars() {
        let pattern = Pattern::Tuple {
            patterns: vec![
                Pattern::Var(Name::mk_simple("x")),
                Pattern::Var(Name::mk_simple("y")),
                Pattern::Wildcard,
                Pattern::Var(Name::mk_simple("z")),
            ],
        };

        let bound_vars = collect_bound_vars(&pattern);
        assert_eq!(bound_vars.len(), 3);
        assert!(bound_vars.contains(&Name::mk_simple("x")));
        assert!(bound_vars.contains(&Name::mk_simple("y")));
        assert!(bound_vars.contains(&Name::mk_simple("z")));
    }

    #[test]
    fn test_nested_tuple_pattern() {
        // Test nested tuple pattern: ((a, b), c)
        let pattern = Pattern::Tuple {
            patterns: vec![
                Pattern::Tuple {
                    patterns: vec![
                        Pattern::Var(Name::mk_simple("a")),
                        Pattern::Var(Name::mk_simple("b")),
                    ],
                },
                Pattern::Var(Name::mk_simple("c")),
            ],
        };

        let bound_vars = collect_bound_vars(&pattern);
        assert_eq!(bound_vars.len(), 3);
        assert!(bound_vars.contains(&Name::mk_simple("a")));
        assert!(bound_vars.contains(&Name::mk_simple("b")));
        assert!(bound_vars.contains(&Name::mk_simple("c")));
    }

    #[test]
    fn test_empty_tuple_pattern() {
        use lean_syn_expr::{SourcePos, SourceRange, SyntaxAtom, SyntaxNode};

        // Test unit pattern: ()
        let pattern_node = SyntaxNode::new(
            SyntaxKind::TuplePattern,
            SourceRange {
                start: SourcePos::new(0, 0, 0),
                end: SourcePos::new(0, 0, 0),
            },
            vec![
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new("("),
                )),
                Syntax::Atom(SyntaxAtom::new(
                    SourceRange {
                        start: SourcePos::new(0, 0, 0),
                        end: SourcePos::new(0, 0, 0),
                    },
                    eterned::BaseCoword::new(")"),
                )),
            ]
            .into(),
        );

        let pattern = compile_tuple_pattern(&pattern_node).unwrap();

        match pattern {
            Pattern::Tuple { patterns } => {
                assert_eq!(patterns.len(), 0);
            }
            _ => panic!("Expected empty tuple pattern"),
        }
    }

    #[test]
    fn test_guarded_pattern_var() {
        use lean_kernel::{Expr, Name};

        // Test variable pattern with guard: x if x > 0
        let guard = GuardCondition::Compare {
            op: ComparisonOp::Greater,
            left: Expr::fvar(Name::mk_simple("x")),
            right: Expr::nat(0),
        };

        let pattern = Pattern::Guarded {
            pattern: Box::new(Pattern::Var(Name::mk_simple("x"))),
            guard,
        };

        let bound_vars = collect_bound_vars(&pattern);
        assert_eq!(bound_vars.len(), 1);
        assert!(bound_vars.contains(&Name::mk_simple("x")));
    }

    #[test]
    fn test_guarded_pattern_literal() {
        use lean_kernel::{Expr, Name};

        // Test literal pattern with guard: 5 if someCondition
        let guard = GuardCondition::BoolExpr(Expr::fvar(Name::mk_simple("someCondition")));

        let pattern = Pattern::Guarded {
            pattern: Box::new(Pattern::Literal(Literal::Nat(5))),
            guard,
        };

        let bound_vars = collect_bound_vars(&pattern);
        assert_eq!(bound_vars.len(), 0); // Literal patterns don't bind
                                         // variables
    }

    #[test]
    fn test_guard_condition_compilation() {
        use lean_kernel::{Expr, Name};

        let mut state = ElabState::new();

        // Test boolean expression guard
        let bool_guard = GuardCondition::BoolExpr(Expr::fvar(Name::mk_simple("condition")));
        let result = compile_guard_condition(&bool_guard, &mut state);
        assert!(result.is_ok());

        // Test equality guard
        let eq_guard = GuardCondition::Equals {
            expr: Expr::fvar(Name::mk_simple("x")),
            value: Expr::nat(42),
        };
        let result = compile_guard_condition(&eq_guard, &mut state);
        assert!(result.is_ok());

        // Test comparison guard
        let comp_guard = GuardCondition::Compare {
            op: ComparisonOp::Greater,
            left: Expr::fvar(Name::mk_simple("x")),
            right: Expr::nat(10),
        };
        let result = compile_guard_condition(&comp_guard, &mut state);
        assert!(result.is_ok());
    }

    #[test]
    fn test_nested_guarded_pattern() {
        use lean_kernel::{Expr, Name};

        // Test tuple pattern with guarded element: (x if x > 0, y)
        let guarded_element = Pattern::Guarded {
            pattern: Box::new(Pattern::Var(Name::mk_simple("x"))),
            guard: GuardCondition::Compare {
                op: ComparisonOp::Greater,
                left: Expr::fvar(Name::mk_simple("x")),
                right: Expr::nat(0),
            },
        };

        let tuple_pattern = Pattern::Tuple {
            patterns: vec![guarded_element, Pattern::Var(Name::mk_simple("y"))],
        };

        let bound_vars = collect_bound_vars(&tuple_pattern);
        assert_eq!(bound_vars.len(), 2);
        assert!(bound_vars.contains(&Name::mk_simple("x")));
        assert!(bound_vars.contains(&Name::mk_simple("y")));
    }

    #[test]
    fn test_guard_compilation_simple() {
        use lean_kernel::{Expr, Name};

        let mut state = ElabState::new();

        // Test simple guarded variable pattern compilation
        let discriminant = Expr::fvar(Name::mk_simple("input"));
        let body = Expr::fvar(Name::mk_simple("result"));

        let guard = GuardCondition::Compare {
            op: ComparisonOp::Greater,
            left: Expr::fvar(Name::mk_simple("x")),
            right: Expr::nat(0),
        };

        let pattern = Pattern::Var(Name::mk_simple("x"));

        let result = compile_guarded_pattern_to_expr(
            discriminant,
            &pattern,
            &guard,
            body,
            vec![], // no rest arms
            &mut state,
        );

        assert!(result.is_ok());
        let expr = result.unwrap();

        // Should be a let expression binding x
        match &expr.kind {
            lean_kernel::expr::ExprKind::Let(name, _, _, _) => {
                assert_eq!(name.to_string(), "x");
            }
            _ => panic!("Expected let expression for guarded variable pattern"),
        }
    }
}
