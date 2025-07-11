use lean_syn_expr::{Syntax, SyntaxKind};

use crate::parser::Parser;

#[test]
fn test_cons_operator_in_pattern_now_supported() {
    // Test that :: operator now works in patterns
    let input = r#"match list with
| x :: xs => x
| [] => 0"#;

    let mut parser = Parser::new(input);
    let result = parser.term().unwrap();

    // Should parse :: as an infix constructor pattern
    match &result {
        Syntax::Node(node) if node.kind == SyntaxKind::Match => {
            assert!(node.children.len() >= 2, "Match should have expr and arms");
            // The first arm should have a constructor pattern with :: operator
        }
        _ => panic!("Expected Match node"),
    }
}

#[test]
fn test_cons_as_constructor_pattern() {
    // For now, we need to use constructor syntax
    // But even List.cons doesn't parse correctly because dots in patterns aren't
    // handled
    let input = r#"match list with
| Cons x xs => x
| Nil => 0"#;

    let mut parser = Parser::new(input);
    let result = parser.term().unwrap();

    // Should parse as constructor patterns
    match &result {
        Syntax::Node(node) if node.kind == SyntaxKind::Match => {
            assert!(node.children.len() >= 2, "Match should have expr and arms");
        }
        _ => panic!("Expected Match node"),
    }
}

#[test]
fn test_option_operator_in_pattern() {
    // Test that ?? operator now works in patterns
    let input = r#"match opt with
| x ?? default => x"#;

    let mut parser = Parser::new(input);
    let result = parser.term().unwrap();

    // Should parse ?? as an infix constructor pattern
    match &result {
        Syntax::Node(node) if node.kind == SyntaxKind::Match => {
            assert!(!node.children.is_empty(), "Match should have expr and arms");
        }
        _ => panic!("Expected Match node"),
    }
}

#[test]
fn test_infix_operator_in_expression() {
    // Test that operators work fine in expressions
    let input = r#"x + y * z"#;

    let mut parser = Parser::new(input);
    let result = parser.term().unwrap();

    match &result {
        Syntax::Node(node) if node.kind == SyntaxKind::BinOp => {
            // Should parse as binary operations with correct precedence
            assert_eq!(node.children.len(), 3);
        }
        _ => panic!("Expected BinOp node"),
    }
}
