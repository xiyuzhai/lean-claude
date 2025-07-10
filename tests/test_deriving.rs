#![allow(clippy::uninlined_format_args)]

#[test]
fn test_inductive_deriving() {
    use lean_parser::Parser;
    use lean_syn_expr::{Syntax, SyntaxKind};

    let input = r#"inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
deriving Repr, BEq, Hashable"#;

    println!("Testing inductive with deriving:");
    println!("{}", input);

    let mut parser = Parser::new(input);
    let result = parser.command();

    match result {
        Ok(Syntax::Node(node)) if node.kind == SyntaxKind::Inductive => {
            println!("✓ Inductive with deriving parsed successfully");
            println!("  Contains {} children", node.children.len());

            // Debug: print all children
            for (i, child) in node.children.iter().enumerate() {
                match child {
                    Syntax::Node(n) => println!("    Child {}: {:?}", i, n.kind),
                    Syntax::Atom(a) => println!("    Child {}: Atom({})", i, a.value.as_str()),
                    _ => println!("    Child {}: Other", i),
                }
            }

            // Find the deriving clause (should be the last child)
            let deriving_child = node.children.last().unwrap();
            match deriving_child {
                Syntax::Node(deriving_node) if deriving_node.kind == SyntaxKind::Deriving => {
                    println!(
                        "  ✓ Found deriving clause with {} typeclasses",
                        deriving_node.children.len()
                    );

                    // Check the typeclass names
                    assert_eq!(deriving_node.children.len(), 3);

                    if let Syntax::Atom(atom) = &deriving_node.children[0] {
                        assert_eq!(atom.value.as_str(), "Repr");
                    }
                    if let Syntax::Atom(atom) = &deriving_node.children[1] {
                        assert_eq!(atom.value.as_str(), "BEq");
                    }
                    if let Syntax::Atom(atom) = &deriving_node.children[2] {
                        assert_eq!(atom.value.as_str(), "Hashable");
                    }

                    println!("  ✓ All typeclass names correct");
                }
                _ => panic!("Expected deriving clause as last child"),
            }
        }
        Ok(_) => panic!("Expected Inductive node"),
        Err(e) => {
            println!("✗ Parse error: {:?}", e);
            panic!("Failed to parse inductive with deriving");
        }
    }
}

#[test]
fn test_structure_deriving() {
    use lean_parser::Parser;
    use lean_syn_expr::{Syntax, SyntaxKind};

    let input = r#"structure Point where
  x : Float
  y : Float
deriving Repr, ToString"#;

    println!("Testing structure with deriving:");
    println!("{}", input);

    let mut parser = Parser::new(input);
    let result = parser.command();

    match result {
        Ok(Syntax::Node(node)) if node.kind == SyntaxKind::Structure => {
            println!("✓ Structure with deriving parsed successfully");

            // Find the deriving clause (should be the last child)
            let deriving_child = node.children.last().unwrap();
            match deriving_child {
                Syntax::Node(deriving_node) if deriving_node.kind == SyntaxKind::Deriving => {
                    println!(
                        "  ✓ Found deriving clause with {} typeclasses",
                        deriving_node.children.len()
                    );
                    assert_eq!(deriving_node.children.len(), 2);
                }
                _ => panic!("Expected deriving clause as last child"),
            }
        }
        Ok(_) => panic!("Expected Structure node"),
        Err(e) => {
            println!("✗ Parse error: {:?}", e);
            panic!("Failed to parse structure with deriving");
        }
    }
}

#[test]
fn test_inductive_without_deriving() {
    use lean_parser::Parser;
    use lean_syn_expr::{Syntax, SyntaxKind};

    let input = r#"inductive Nat where
  | zero : Nat
  | succ : Nat → Nat"#;

    let mut parser = Parser::new(input);
    let result = parser.command();

    match result {
        Ok(Syntax::Node(node)) if node.kind == SyntaxKind::Inductive => {
            println!("✓ Inductive without deriving parsed successfully");

            // Should not have a deriving clause
            // Check that none of the children are deriving nodes
            let has_deriving = node
                .children
                .iter()
                .any(|child| matches!(child, Syntax::Node(n) if n.kind == SyntaxKind::Deriving));
            assert!(!has_deriving, "Should not have deriving clause");
        }
        Ok(_) => panic!("Expected Inductive node"),
        Err(e) => panic!("Failed to parse inductive: {:?}", e),
    }
}
