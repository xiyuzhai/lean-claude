use lean_parser::Parser;

#[test]
fn test_simple_def() {
    let input = "def result := myif true then 1 else 2";

    let mut parser = Parser::new(input);
    let def_cmd = parser.def_command();

    match &def_cmd {
        Ok(d) => println!("Def success: {d:#?}"),
        Err(e) => println!("Def error: {e:?}"),
    }

    assert!(def_cmd.is_ok());
}

#[test]
fn test_term_parsing() {
    let input = "myif true then 1 else 2";

    let mut parser = Parser::new(input);
    let term = parser.term();

    match &term {
        Ok(t) => println!("Term success: {t:#?}"),
        Err(e) => println!("Term error: {e:?}"),
    }

    assert!(term.is_ok());
}
