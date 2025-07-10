use lean_parser::Parser;

#[test]
fn test_error_cases() {
    let inputs_with_errors = vec![
        ("def foo := ", "Missing body"),
        ("theorem bar :", "Missing type and proof"),
        ("match x with", "Missing match arms"),
        ("λ", "Incomplete lambda"),
        ("∀ x :", "Missing type and body"),
    ];

    for (input, description) in inputs_with_errors {
        println!("\nTesting error case: {} - {}", input, description);
        let mut parser = Parser::new(input);
        
        // Try parsing as module
        let module_result = parser.module();
        match &module_result {
            Ok(syntax) => {
                println!("  Module: Parsed successfully");
                println!("  Kind: {:?}", syntax.kind());
                if syntax.is_missing() {
                    println!("  Contains missing nodes!");
                }
            }
            Err(e) => {
                println!("  Module: Error as expected - {:?}", e);
            }
        }
        
        // Try parsing as command
        let mut parser2 = Parser::new(input);
        let cmd_result = parser2.command();
        match &cmd_result {
            Ok(syntax) => {
                println!("  Command: Parsed successfully");
                println!("  Kind: {:?}", syntax.kind());
            }
            Err(e) => {
                println!("  Command: Error - {:?}", e);
            }
        }
        
        // Try parsing as term
        let mut parser3 = Parser::new(input);
        let term_result = parser3.term();
        match &term_result {
            Ok(syntax) => {
                println!("  Term: Parsed successfully");
                println!("  Kind: {:?}", syntax.kind());
            }
            Err(e) => {
                println!("  Term: Error - {:?}", e);
            }
        }
    }
}