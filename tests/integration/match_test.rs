use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
fn test_match_expressions() {
    let test_cases = vec![
        // Basic match with variable pattern
        ("match n with | x => x", "variable pattern", true),
        // Match with wildcard
        ("match n with | _ => 0", "wildcard pattern", true),
        // Match with literal pattern
        ("match n with | 0 => true", "literal pattern", true),
        // Match with multiple arms
        ("match n with | 0 => true | _ => false", "multiple arms", true),
        // Match with constructor pattern
        ("match n with | some x => x | none => 0", "constructor pattern", true),
    ];
    
    for (input, description, should_parse) in test_cases {
        println!("\nTesting: {} - {}", input, description);
        let mut parser = Parser::new(input);
        let result = parser.term();
        
        match (result, should_parse) {
            (Ok(syntax), true) => {
                println!("  ✓ Parsed successfully as {:?}", syntax.kind());
                if let Syntax::Node(node) = &syntax {
                    println!("  Arms: {}", node.children.len() - 1); // -1 for scrutinee
                }
            }
            (Ok(_), false) => {
                println!("  ! Parsed but expected failure");
            }
            (Err(e), true) => {
                println!("  ✗ Failed but expected success: {:?}", e);
            }
            (Err(e), false) => {
                println!("  ✓ Failed as expected: {:?}", e);
            }
        }
    }
}

#[test]
fn test_pattern_parsing() {
    let patterns = vec![
        ("x", "variable", true),
        ("_", "wildcard", true),
        ("0", "literal", true),
        ("42", "number literal", true),
        ("\"hello\"", "string literal", true),
        ("Cons x xs", "constructor", true),
        ("(x, y)", "tuple", true),
    ];
    
    for (input, description, should_parse) in patterns {
        println!("\nTesting pattern: {} - {}", input, description);
        let mut parser = Parser::new(input);
        let result = parser.pattern();
        
        match (result, should_parse) {
            (Ok(syntax), true) => {
                println!("  ✓ Parsed pattern successfully");
                println!("  Kind: {:?}", syntax.kind());
            }
            (Ok(_), false) => {
                println!("  ! Parsed but expected failure");
            }
            (Err(e), true) => {
                println!("  ✗ Failed: {:?}", e);
            }
            (Err(_), false) => {
                println!("  ✓ Failed as expected");
            }
        }
    }
}