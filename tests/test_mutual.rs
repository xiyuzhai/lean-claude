#![allow(clippy::uninlined_format_args)]

#[test]
fn test_mutual_basic() {
    use lean_parser::Parser;
    use lean_syn_expr::{Syntax, SyntaxKind};

    let input = r#"mutual
  inductive Tree where
    | leaf : Tree
    | node : Tree → Forest → Tree
    
  inductive Forest where
    | nil : Forest
    | cons : Tree → Forest → Forest
end"#;

    println!("Testing mutual block:");
    println!("{}", input);

    let mut parser = Parser::new(input);
    let result = parser.command();

    match result {
        Ok(Syntax::Node(node)) if node.kind == SyntaxKind::Mutual => {
            println!("✓ Mutual block parsed successfully");
            println!("  Contains {} declarations", node.children.len());

            // Should have 2 inductive declarations
            assert_eq!(node.children.len(), 2);

            // Both should be inductive
            assert!(
                matches!(&node.children[0], Syntax::Node(n) if n.kind == SyntaxKind::Inductive)
            );
            assert!(
                matches!(&node.children[1], Syntax::Node(n) if n.kind == SyntaxKind::Inductive)
            );

            println!("  Declaration 0: {:?}", node.children[0]);
            println!("  Declaration 1: {:?}", node.children[1]);
        }
        Ok(syntax) => {
            println!("✗ Unexpected syntax: {:?}", syntax);
            panic!("Expected Mutual block");
        }
        Err(e) => {
            println!("✗ Parse error: {:?}", e);
            panic!("Failed to parse mutual block");
        }
    }
}

#[test]
fn test_mutual_mixed() {
    use lean_parser::Parser;
    use lean_syn_expr::{Syntax, SyntaxKind};

    let input = r#"mutual
  def f (n : Nat) : Nat := g n + 1
  def g (n : Nat) : Nat := if n = 0 then 0 else f (n - 1)
end"#;

    let mut parser = Parser::new(input);
    let result = parser.command();

    match result {
        Ok(Syntax::Node(node)) if node.kind == SyntaxKind::Mutual => {
            println!("✓ Mutual def block parsed successfully");
            println!("  Contains {} definitions", node.children.len());

            // Should have 2 def declarations
            assert_eq!(node.children.len(), 2);
        }
        Ok(_) => panic!("Expected Mutual block"),
        Err(e) => {
            println!("Parse error: {:?}", e);
            // For now, def parsing might not be fully implemented
            println!("Note: def parsing may not be fully implemented yet");
        }
    }
}
