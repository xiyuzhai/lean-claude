#[test]
fn test_module_parsing() {
    use lean_parser::Parser;
    
    let input = "structure A where\n  x : Nat\n\ninductive B where\n  | b";
    
    println!("Input: {:?}", input);
    println!("Input bytes: {:?}", input.as_bytes());
    
    let mut parser = Parser::new(input);
    
    // Manually trace through module parsing
    println!("\n1. Initial skip whitespace");
    parser.skip_whitespace_and_comments();
    println!("   Position: {:?}", parser.position());
    println!("   At end: {}", parser.input().is_at_end());
    
    println!("\n2. Parse first command");
    let cmd1 = parser.command();
    println!("   Result: {}", cmd1.is_ok());
    println!("   Position after: {:?}", parser.position());
    
    println!("\n3. Skip whitespace again"); 
    parser.skip_whitespace_and_comments();
    println!("   Position: {:?}", parser.position());
    println!("   At end: {}", parser.input().is_at_end());
    println!("   Next char: {:?}", parser.peek());
    
    println!("\n4. Parse second command");
    let cmd2 = parser.command();
    match &cmd2 {
        Ok(_) => println!("   Result: OK"),
        Err(e) => {
            println!("   Result: Error - {:?}", e.kind);
            println!("   Error position: {:?}", e.position);
        }
    }
}