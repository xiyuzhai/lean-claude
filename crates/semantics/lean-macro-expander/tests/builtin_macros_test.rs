//! Tests for built-in macros (panic!, assert!, unreachable!, dbg!)

use expect_test::{expect, Expect};
use lean_macro_expander::{MacroEnvironment, MacroExpander};
use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

fn check_builtin_expansion(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let module = parser.module().expect("Failed to parse");

    // Create expander with built-in macros
    let env = MacroEnvironment::new();
    let mut expander = MacroExpander::new(env);

    match expander.expand(&module) {
        Ok(expanded) => {
            let output = format_syntax(&expanded);
            expected.assert_eq(&output);
        }
        Err(e) => {
            expected.assert_eq(&format!("Error: {e}"));
        }
    }
}

fn format_syntax(syntax: &Syntax) -> String {
    match syntax {
        Syntax::Missing => "<missing>".to_string(),
        Syntax::Atom(atom) => atom.value.to_string(),
        Syntax::Node(node) => {
            let kind = format!("{:?}", node.kind);
            if node.children.is_empty() {
                format!("({kind})")
            } else {
                let children: Vec<String> = node
                    .children
                    .iter()
                    .filter(|child| {
                        // Filter out whitespace and comments for cleaner output
                        match child {
                            Syntax::Node(n) => {
                                n.kind != SyntaxKind::Whitespace && n.kind != SyntaxKind::Comment
                            }
                            _ => true,
                        }
                    })
                    .map(format_syntax)
                    .collect();
                if children.is_empty() {
                    format!("({kind})")
                } else {
                    format!("({} {})", kind, children.join(" "))
                }
            }
        }
    }
}

#[test]
fn test_panic_macro() {
    check_builtin_expansion(
        "def test := panic! \"something went wrong\"",
        expect![[r#"(Module (Def test (App panic something went wrong)))"#]],
    );
}

#[test]
fn test_panic_macro_with_interpolation() {
    check_builtin_expansion(
        "def test (x : Nat) := panic! \"error: {x}\"",
        expect![[r#"(Module (Def test (LeftParen x Nat) (App panic error: {x})))"#]],
    );
}

#[test]
fn test_unreachable_macro() {
    check_builtin_expansion(
        "def test := if true then 1 else unreachable!",
        expect![[r#"(Module (Def test (Match true 1 (App panic "unreachable code"))))"#]],
    );
}

#[test]
fn test_unreachable_in_match() {
    check_builtin_expansion(
        "def test (x : Option Nat) := match x with | some n => n | none => unreachable!",
        expect![[
            r#"(Module (Def test (LeftParen x (App Option Nat)) (Match x (MatchArm (ConstructorPattern some n) n) (MatchArm none (App panic "unreachable code")))))"#
        ]],
    );
}

#[test]
fn test_assert_macro() {
    check_builtin_expansion(
        "def test := assert! (1 < 2)",
        expect![[
            r#"(Module (Def test (App if (BinOp 1 < 2) then () else (App panic "assertion failed"))))"#
        ]],
    );
}

#[test]
fn test_assert_with_complex_condition() {
    check_builtin_expansion(
        "def test (x y : Nat) := assert! (x + y > 0)",
        expect![[
            r#"(Module (Def test (LeftParen x y Nat) (App if (BinOp (BinOp x + y) > 0) then () else (App panic "assertion failed"))))"#
        ]],
    );
}

#[test]
fn test_dbg_macro() {
    // For now, dbg! just returns the expression (will add trace! later)
    check_builtin_expansion(
        "def test := dbg! (1 + 2)",
        expect![[r#"(Module (Def test (BinOp 1 + 2)))"#]],
    );
}

#[test]
fn test_dbg_with_variable() {
    check_builtin_expansion(
        "def test (x : Nat) := dbg! x",
        expect![[r#"(Module (Def test (LeftParen x Nat) x))"#]],
    );
}

#[test]
fn test_multiple_builtins() {
    check_builtin_expansion(
        r#"def test (x : Nat) := 
  let y := dbg! (x + 1)
  assert! (y > 0)
  if y = 0 then unreachable! else y"#,
        expect![[r#"(Module)"#]],
    );
}

#[test]
fn test_nested_builtins() {
    check_builtin_expansion(
        "def test := assert! (dbg! true)",
        expect![[
            r#"(Module (Def test (App if true then () else (App panic "assertion failed"))))"#
        ]],
    );
}

#[test]
fn test_panic_in_function() {
    check_builtin_expansion(
        r#"def divide (x y : Nat) : Nat :=
  if y = 0 then panic! "division by zero" else x / y"#,
        expect![[
            r#"(Module (Def divide (LeftParen x y Nat) Nat (Match (BinOp y = 0) (App panic division by zero) (BinOp x / y))))"#
        ]],
    );
}

#[test]
fn test_assert_in_proof() {
    check_builtin_expansion(
        "theorem test : 1 + 1 = 2 := by assert! (1 + 1 = 2); rfl",
        expect![[
            r#"(Module (Theorem test (BinOp (BinOp 1 + 1) = 2) (By (TacticSeq (CustomTactic assert! (BinOp (BinOp 1 + 1) = 2)) (Rfl)))))"#
        ]],
    );
}
