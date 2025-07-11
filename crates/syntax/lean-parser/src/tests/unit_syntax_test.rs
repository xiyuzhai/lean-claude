use lean_syn_expr::{Syntax, SyntaxKind};

use crate::parser::Parser;

#[test]
fn test_unit_syntax_parsing() {
    let input = r#"macro "test" : term => `(())"#;
    let mut parser = Parser::new(input);
    let result = parser.module().unwrap();

    // Check that we have a module with one command
    match &result {
        Syntax::Node(node) if node.kind == SyntaxKind::Module => {
            assert_eq!(node.children.len(), 1);

            // Navigate through the macro definition to find the unit syntax
            if let Syntax::Node(cmd) = &node.children[0] {
                // The macro body should contain a quotation with unit
                // We're looking for the App node representing Unit.unit
                let has_unit_app = find_unit_app(&Syntax::Node(cmd.clone()));
                assert!(has_unit_app, "Should find Unit.unit as an App node");
            }
        }
        _ => panic!("Expected Module node"),
    }
}

fn find_unit_app(syntax: &Syntax) -> bool {
    match syntax {
        Syntax::Node(node) => {
            // Check if this is a Unit.unit App node
            if node.kind == SyntaxKind::App && node.children.len() == 2 {
                if let (Syntax::Atom(atom1), Syntax::Atom(atom2)) =
                    (&node.children[0], &node.children[1])
                {
                    if atom1.value.as_str() == "Unit" && atom2.value.as_str() == "unit" {
                        return true;
                    }
                }
            }
            // Also check inside ConstructorPattern nodes
            if node.kind == SyntaxKind::ConstructorPattern {
                for child in &node.children {
                    if find_unit_app(child) {
                        return true;
                    }
                }
            }
            // Recursively search in all children
            node.children.iter().any(find_unit_app)
        }
        _ => false,
    }
}

#[test]
fn test_unit_in_expression() {
    let input = r#"def x : Unit := ()"#;
    let mut parser = Parser::new(input);
    let result = parser.module().unwrap();

    // Verify () is parsed as Unit.unit
    let has_unit = find_unit_app(&result);
    assert!(has_unit, "Should parse () as Unit.unit");
}

#[test]
fn test_unit_in_match() {
    let input = r#"match x with | () => 0"#;
    let mut parser = Parser::new(input);
    let result = parser.term().unwrap();

    // Verify () in pattern is parsed as Unit.unit
    let has_unit = find_unit_app(&result);
    assert!(has_unit, "Should parse () in pattern as Unit.unit");
}
