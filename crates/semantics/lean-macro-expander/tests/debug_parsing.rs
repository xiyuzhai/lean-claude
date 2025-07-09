use lean_parser::Parser;

#[test]
fn test_parse_assert_macro() {
    let input = r#"macro "assert!" cond:term : term => `(if $cond then () else panic!)"#;
    println!("Input length: {}", input.len());
    println!("Character at position 53: {:?}", input.chars().nth(53));

    let mut parser = Parser::new(input);
    match parser.command() {
        Ok(cmd) => println!("Parsed command: {:#?}", cmd),
        Err(e) => println!("Parse error: {:?}", e),
    }

    // Also test the multiline version
    let input2 = r#"
macro "assert!" cond:term : term => `(if $cond then () else panic!)
"#;
    let mut parser2 = Parser::new(input2);
    match parser2.module() {
        Ok(module) => {
            println!("Parsed module: {:#?}", module);
            if let lean_syn_expr::Syntax::Node(node) = &module {
                println!("Module has {} children", node.children.len());
            }
        }
        Err(e) => println!("Module parse error: {:?}", e),
    }
}

#[test]
fn test_parse_simple_module_with_macro() {
    let input = r#"
macro "twice" x:term : term => `($x + $x)
def test := twice 5
"#;

    let mut parser = Parser::new(input);
    match parser.module() {
        Ok(module) => {
            println!("Parsed module: {:#?}", module);
            if let lean_syn_expr::Syntax::Node(node) = &module {
                println!("Module has {} children", node.children.len());
            }
        }
        Err(e) => println!("Parse error: {:?}", e),
    }
}
