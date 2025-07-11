use lean_parser::Parser;

#[test]
fn test_simple_macro_rules() {
    let input = r#"
macro_rules 
| `(myif true then $x else $y) => `($x)
| `(myif false then $x else $y) => `($y)
| `(myif $c then $x else $y) => `(if $c then $x else $y)
"#;

    println!("Input length: {}", input.len());
    println!("Character at offset 150: {:?}", input.chars().nth(150));

    let mut parser = Parser::new(input);

    // Try to parse just the macro_rules command
    parser.skip_whitespace();
    let macro_rules = parser.macro_rules();

    match &macro_rules {
        Ok(m) => println!("MacroRules success: {m:#?}"),
        Err(e) => println!("MacroRules error: {e:?}"),
    }

    assert!(macro_rules.is_ok());
}
