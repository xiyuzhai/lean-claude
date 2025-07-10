use lean_parser::Parser;
use lean_syn_expr::SyntaxKind;

#[test]
fn test_minimal_by() {
    let test_cases = vec![
        ("by sorry", "by sorry"),
        ("by exact h", "by exact"),
        ("by intro x", "by intro single"),
        ("by intro x y", "by intro multi"),
        ("by intro", "by intro no args"),
    ];
    
    for (input, description) in test_cases {
        println!("\nTesting: {} ({})", input, description);
        let mut parser = Parser::new(input);
        let result = parser.term();
        
        match result {
            Ok(syntax) => {
                println!("  Success! Kind: {:?}", syntax.kind());
                if let lean_syn_expr::Syntax::Node(node) = &syntax {
                    println!("  Children: {}", node.children.len());
                    for (i, child) in node.children.iter().enumerate() {
                        println!("    Child {}: {:?}", i, child.kind());
                    }
                }
            }
            Err(e) => {
                println!("  Error: {:?}", e);
            }
        }
    }
}

#[test]
fn test_by_as_identifier() {
    // Make sure "by" alone is not parsed as an identifier
    let input = "by";
    let mut parser = Parser::new(input);
    let result = parser.term();
    
    match result {
        Ok(syntax) => {
            println!("Parsed 'by' alone as: {:?}", syntax.kind());
            if matches!(&syntax, lean_syn_expr::Syntax::Atom(_)) {
                println!("ERROR: 'by' was parsed as an identifier!");
            }
        }
        Err(e) => {
            println!("Expected error when parsing 'by' alone: {:?}", e);
        }
    }
}