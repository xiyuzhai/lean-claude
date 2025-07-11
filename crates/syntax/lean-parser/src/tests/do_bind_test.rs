use lean_syn_expr::{Syntax, SyntaxKind};

use crate::parser::Parser;

#[test]
fn test_do_bind_operator() {
    let input = r#"do
  let x ← getValue
  let y ← readInput
  return x + y"#;

    let mut parser = Parser::new(input);
    let result = parser.term().unwrap();

    // Check that we have a Do node
    match &result {
        Syntax::Node(node) if node.kind == SyntaxKind::Do => {
            // Should have 3 statements
            assert_eq!(node.children.len(), 3);

            // First two should be Bind nodes
            for i in 0..2 {
                match &node.children[i] {
                    Syntax::Node(stmt) if stmt.kind == SyntaxKind::Bind => {
                        // Good, we have bind nodes
                    }
                    _ => panic!("Expected Bind node at position {i}"),
                }
            }

            // Last should be return statement
            match &node.children[2] {
                Syntax::Node(stmt) if stmt.kind == SyntaxKind::Return => {
                    // Good, we have return
                }
                _ => panic!("Expected Return node"),
            }
        }
        _ => panic!("Expected Do node, got: {result:?}"),
    }
}

#[test]
fn test_do_bind_alternative_syntax() {
    let input = r#"do
  let x <- getValue
  let y <- readInput
  return x + y"#;

    let mut parser = Parser::new(input);
    let result = parser.term().unwrap();

    // Check that we have a Do node
    match &result {
        Syntax::Node(node) if node.kind == SyntaxKind::Do => {
            // Should have 3 statements
            assert_eq!(node.children.len(), 3);

            // First two should be Bind nodes
            for i in 0..2 {
                match &node.children[i] {
                    Syntax::Node(stmt) if stmt.kind == SyntaxKind::Bind => {
                        // Good, we have bind nodes
                    }
                    _ => panic!("Expected Bind node at position {i}"),
                }
            }
        }
        _ => panic!("Expected Do node"),
    }
}
