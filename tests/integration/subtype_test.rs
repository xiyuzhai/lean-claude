use lean_parser::Parser;
use lean_syn_expr::SyntaxKind;

#[test]
fn test_subtype_parsing() {
    let test_cases = vec![
        ("{x : Nat // x > 0}", "basic subtype"),
        ("{x // x > 0}", "subtype without type annotation"),
        ("{x : Nat // True}", "subtype with simple predicate"),
        ("{(x, y) : Nat × Nat // x < y}", "subtype with pair"),
    ];
    
    for (input, description) in test_cases {
        println!("\nTesting: {} - {}", input, description);
        let mut parser = Parser::new(input);
        let result = parser.term();
        
        match result {
            Ok(syntax) => {
                println!("  ✓ Parsed successfully as {:?}", syntax.kind());
                if syntax.kind() != Some(SyntaxKind::Subtype) {
                    println!("  ⚠ Warning: Expected Subtype, got {:?}", syntax.kind());
                }
            }
            Err(e) => {
                println!("  ✗ Failed: {:?}", e);
                
                // Try parsing just the binder part
                println!("  Debugging: trying to parse '{{x : Nat' part...");
                let mut parser2 = Parser::new("{x : Nat");
                let result2 = parser2.implicit_term();
                match result2 {
                    Ok(_) => println!("    Binder part parsed OK"),
                    Err(e2) => println!("    Binder part failed: {:?}", e2),
                }
            }
        }
    }
}