use lean_parser::Parser;

fn main() {
    let input = r#"
macro_rules 
| `(myif true then $x else $y) => `($x)
| `(myif false then $x else $y) => `($y)
| `(myif $c then $x else $y) => `(if $c then $x else $y)
"#;

    let mut parser = Parser::new(input);
    let module = parser.module();
    
    match module {
        Ok(m) => println!("Success: {m:#?}"),
        Err(e) => println!("Error: {e:?}"),
    }
}