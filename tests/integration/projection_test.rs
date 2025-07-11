use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
fn test_numeric_projection() {
    let input = "x.1";
    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(result.is_ok(), "Failed to parse: {result:?}");
    let syntax = result.unwrap();

    if let Syntax::Node(node) = &syntax {
        assert_eq!(node.kind, SyntaxKind::Projection);
        assert_eq!(node.children.len(), 2);

        // Check that we have x and 1
        if let Syntax::Atom(atom) = &node.children[0] {
            assert_eq!(atom.value.as_str(), "x");
        }
        if let Syntax::Atom(atom) = &node.children[1] {
            assert_eq!(atom.value.as_str(), "1");
        }
    } else {
        panic!("Expected projection node");
    }
}

#[test]
fn test_field_projection() {
    let input = "x.field";
    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(result.is_ok(), "Failed to parse: {result:?}");
    let syntax = result.unwrap();

    if let Syntax::Node(node) = &syntax {
        assert_eq!(node.kind, SyntaxKind::Projection);
        assert_eq!(node.children.len(), 2);
    } else {
        panic!("Expected projection node");
    }
}

#[test]
fn test_nested_projection() {
    let input = "x.field.subfield";
    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(result.is_ok(), "Failed to parse: {result:?}");
    let syntax = result.unwrap();

    // Should be projection(projection(x, field), subfield)
    if let Syntax::Node(outer) = &syntax {
        assert_eq!(outer.kind, SyntaxKind::Projection);
        assert_eq!(outer.children.len(), 2);

        // Check inner projection
        if let Syntax::Node(inner) = &outer.children[0] {
            assert_eq!(inner.kind, SyntaxKind::Projection);
        }
    } else {
        panic!("Expected nested projection");
    }
}

#[test]
fn test_projection_with_application() {
    let input = "f x.1 y.field";
    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(result.is_ok(), "Failed to parse: {result:?}");
    let syntax = result.unwrap();

    // Should be App(f, projection(x, 1), projection(y, field))
    if let Syntax::Node(app) = &syntax {
        assert_eq!(app.kind, SyntaxKind::App);
        println!("App has {} children", app.children.len());
        for (i, child) in app.children.iter().enumerate() {
            println!(
                "Child {}: {:?}",
                i,
                match child {
                    Syntax::Atom(atom) => format!("Atom({})", atom.value),
                    Syntax::Node(node) => format!("Node({:?})", node.kind),
                    Syntax::Missing => "Missing".to_string(),
                }
            );
        }
        assert_eq!(app.children.len(), 3);

        // Check second argument is projection
        if let Syntax::Node(proj1) = &app.children[1] {
            assert_eq!(proj1.kind, SyntaxKind::Projection);
        }

        // Check third argument is projection
        if let Syntax::Node(proj2) = &app.children[2] {
            assert_eq!(proj2.kind, SyntaxKind::Projection);
        }
    } else {
        panic!("Expected application");
    }
}

#[test]
fn test_projection_with_parentheses() {
    let input = "(x + y).field";
    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(result.is_ok(), "Failed to parse: {result:?}");
    let syntax = result.unwrap();

    // Should be projection(binop(+, x, y), field)
    if let Syntax::Node(proj) = &syntax {
        assert_eq!(proj.kind, SyntaxKind::Projection);

        // Check that first child is a binary operation
        if let Syntax::Node(binop) = &proj.children[0] {
            assert_eq!(binop.kind, SyntaxKind::BinOp);
        }
    } else {
        panic!("Expected projection");
    }
}

#[test]
fn test_tuple_projections() {
    let cases = vec![
        ("p.1", "first projection"),
        ("p.2", "second projection"),
        ("triple.3", "third projection"),
    ];

    for (input, desc) in cases {
        let mut parser = Parser::new(input);
        let result = parser.term();
        assert!(result.is_ok(), "Failed to parse {desc}: {result:?}");

        if let Ok(Syntax::Node(node)) = result {
            assert_eq!(
                node.kind,
                SyntaxKind::Projection,
                "Expected projection for {desc}"
            );
        }
    }
}

#[test]
fn test_projection_not_confused_with_range() {
    // Make sure x.1 is parsed as projection, not confused with x..1
    let input = "x.1";
    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(result.is_ok());
    if let Ok(Syntax::Node(node)) = result {
        assert_eq!(node.kind, SyntaxKind::Projection);
    }

    // x..1 should not be parsed as projection
    let input2 = "x..1";
    let mut parser2 = Parser::new(input2);
    let result2 = parser2.term();

    // This might fail or parse differently - that's expected
    if let Ok(Syntax::Node(node)) = result2 {
        assert_ne!(
            node.kind,
            SyntaxKind::Projection,
            "x..1 should not be a projection"
        );
    }
}
