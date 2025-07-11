use lean_parser::Parser;

#[test]
fn test_debug_macro_rules() {
    let input = r#"
macro_rules 
| `(myif $x) => `(match $x with | true => 1 | false => 2)
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();

    match result {
        Ok(module) => {
            println!("Successfully parsed module:");
            println!("{module:#?}");
        }
        Err(e) => {
            println!("Parse error: {e:#?}");
        }
    }
}
