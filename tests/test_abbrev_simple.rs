#![allow(clippy::uninlined_format_args)]

#[test]
fn test_abbrev_simple() {
    use lean_parser::Parser;

    // Test just abbrev
    let input = "abbrev Origin := Point.mk 0 0";

    println!("Testing abbrev: {}", input);

    let mut parser = Parser::new(input);
    let result = parser.command();

    match result {
        Ok(_) => println!("✓ OK"),
        Err(e) => {
            println!("✗ Error: {:?}", e);
            println!("  Position: {:?}", e.position);

            // Let's trace through manually
            let mut p2 = Parser::new(input);
            p2.keyword("abbrev").unwrap();
            p2.skip_whitespace();
            println!("  After 'abbrev': next char is {:?}", p2.peek());

            let name = p2.identifier().unwrap();
            println!("  Parsed name: {:?}", name);
            p2.skip_whitespace();
            println!("  After name: next char is {:?}", p2.peek());

            // Check for :=
            if p2.peek() == Some(':') && p2.input().peek_nth(1) == Some('=') {
                println!("  Found ':='");
            } else {
                println!(
                    "  No ':=' found. Next chars: {:?} {:?}",
                    p2.peek(),
                    p2.input().peek_nth(1)
                );
            }
        }
    }
}
