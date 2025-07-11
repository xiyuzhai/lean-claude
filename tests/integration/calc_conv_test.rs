#![allow(clippy::uninlined_format_args)]

use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
fn test_calc_mode() {
    let test_cases = vec![
        // Basic calc
        (
            r#"calc a = b := by rw [h1]
     _ = c := by rw [h2]"#,
            "basic calc with tactics",
        ),
        // Calc with different relations
        (
            r#"calc a < b := lt_proof
     _ ≤ c := le_proof
     _ = d := eq_proof"#,
            "calc with mixed relations",
        ),
        // Calc in term position
        (
            r#"theorem foo : a = d := calc
  a = b := ab_proof
  _ = c := bc_proof
  _ = d := cd_proof"#,
            "calc in theorem",
        ),
        // Calc with complex proofs
        (
            r#"calc w = x := by ring
     _ = z := by simp [h]"#,
            "calc with mathlib tactics",
        ),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = if input.starts_with("theorem") {
            parser.command()
        } else {
            parser.term()
        };

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}: {:#?}", description, syntax);
                assert!(
                    contains_calc(&syntax),
                    "Should contain calc node for {}",
                    description
                );
            }
            Err(e) => panic!("Failed to parse {}: {:?}", description, e),
        }
    }
}

#[test]
fn test_conv_mode() {
    let test_cases = vec![
        // Basic conv
        ("conv => lhs; rw [add_comm]", "basic conv with lhs"),
        // Conv with target
        ("conv at h => rhs; simp", "conv at hypothesis"),
        // Conv with multiple steps
        (
            r#"conv in x + y => 
  lhs
  rw [add_comm]
  change y + x"#,
            "conv with multiple tactics",
        ),
        // Conv with arg
        ("conv => arg 2; rw [mul_comm]", "conv with arg selection"),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.tactic();

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}: {:#?}", description, syntax);
                // Conv creates a CustomTactic node
                assert!(
                    matches_syntax_kind(&syntax, SyntaxKind::CustomTactic),
                    "Should be custom tactic for {}",
                    description
                );
            }
            Err(e) => panic!("Failed to parse {}: {:?}", description, e),
        }
    }
}

#[test]
fn test_calc_in_tactic_mode() {
    let input = r#"by
  calc a = b := by exact h1
       _ = c := by rw [h2]
  exact this"#;

    let mut parser = Parser::new(input);
    let result = parser.by_tactic();

    assert!(result.is_ok(), "Should parse calc in tactic mode");
    let syntax = result.unwrap();
    assert!(contains_calc(&syntax), "Should contain calc node");
}

#[test]
fn test_conv_in_tactic_sequence() {
    let input = r#"by
  rw [foo]
  conv at h => lhs; simp
  exact h"#;

    let mut parser = Parser::new(input);
    let result = parser.by_tactic();

    assert!(result.is_ok(), "Should parse conv in tactic sequence");
}

// Helper functions
fn contains_calc(syntax: &Syntax) -> bool {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == SyntaxKind::Calc {
                return true;
            }
            node.children.iter().any(contains_calc)
        }
        _ => false,
    }
}

fn matches_syntax_kind(syntax: &Syntax, kind: SyntaxKind) -> bool {
    match syntax {
        Syntax::Node(node) => node.kind == kind,
        _ => false,
    }
}
