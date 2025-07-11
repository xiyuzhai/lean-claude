use lean_parser::Parser;

#[test]
fn test_macro_rules_with_match() {
    let input = r#"
macro_rules 
| `(myif $x) => `(match $x with | true => 1 | false => 2)
"#;

    let mut parser = Parser::new(input);
    parser.skip_whitespace();
    let macro_rules = parser.macro_rules();

    match &macro_rules {
        Ok(m) => println!("MacroRules success: {m:#?}"),
        Err(e) => println!("MacroRules error: {e:?}"),
    }

    assert!(macro_rules.is_ok());
}

#[test]
fn test_simple_match_quotation() {
    let input = r#"`(match $x with | true => 1 | false => 2)"#;

    let mut parser = Parser::new(input);
    let result = parser.parse_syntax_quotation();

    match &result {
        Ok(q) => println!("Simple quotation success: {q:#?}"),
        Err(e) => println!("Simple quotation error: {e:?}"),
    }

    assert!(result.is_ok());
}
