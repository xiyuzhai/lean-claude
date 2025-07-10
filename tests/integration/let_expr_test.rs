use lean_parser::Parser;
use lean_syn_expr::SyntaxKind;

#[test]
fn test_let_expressions() {
    let test_cases = vec![
        // Standard let with 'in'
        ("let x := 5 in x * 2", "let with in", true),
        // Let without 'in' (should parse x * 2 as the body)
        ("let x := 5 x * 2", "let without in", true),
        // Let with type annotation
        ("let x : Nat := 5 in x * 2", "let with type", true),
        // Semicolon-separated (this is not a single let expression)
        ("let x := 5; x * 2", "let with semicolon", false),
        // Parenthesized version
        ("(let x := 5; x * 2)", "parenthesized let sequence", false),
    ];
    
    for (input, description, should_succeed) in test_cases {
        println!("\nTesting: {} - {}", input, description);
        let mut parser = Parser::new(input);
        let result = parser.term();
        
        match (result, should_succeed) {
            (Ok(syntax), true) => {
                println!("  ✓ Parsed successfully as {:?}", syntax.kind());
            }
            (Ok(syntax), false) => {
                println!("  ! Parsed but expected failure: {:?}", syntax.kind());
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