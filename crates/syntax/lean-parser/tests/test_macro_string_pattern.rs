use lean_parser::Parser;
use lean_syn_expr::Syntax;

#[test]
fn test_macro_string_pattern() {
    let test_cases = vec![
        ("macro \"test\" : term => `(42)", "simple string pattern"),
        (
            "macro \"double\" x:term : term => `($x + $x)",
            "string pattern with param",
        ),
        (
            "macro \"∀∀\" xs:ident* \",\" b:term : term => `(test)",
            "string pattern with multiple params",
        ),
    ];

    for (input, desc) in test_cases {
        println!("\nTesting: {desc} - {input}");
        let mut parser = Parser::new(input);

        match parser.macro_def() {
            Ok(syntax) => {
                println!("✓ Parsed successfully");
                print_syntax(&syntax, 0);
            }
            Err(e) => {
                println!("✗ Parse error: {e:?}");

                // Try parsing just the pattern part
                let pattern_start = input.find('"').unwrap();
                let pattern_input = &input[pattern_start..];
                println!("\nTrying to parse pattern: {pattern_input}");

                let mut pattern_parser = Parser::new(pattern_input);
                match pattern_parser.string_literal() {
                    Ok(_lit) => {
                        println!("String literal parsed OK");
                        pattern_parser.skip_whitespace();

                        // Try to continue parsing parameters
                        println!("Next char: {:?}", pattern_parser.peek());
                    }
                    Err(e) => {
                        println!("String literal error: {e:?}");
                    }
                }
            }
        }
    }
}

fn print_syntax(syntax: &Syntax, indent: usize) {
    let indent_str = " ".repeat(indent);
    match syntax {
        Syntax::Missing => println!("{indent_str}Missing"),
        Syntax::Atom(atom) => println!("{}Atom: {}", indent_str, atom.value),
        Syntax::Node(node) => {
            println!("{}Node: {:?}", indent_str, node.kind);
            for child in &node.children {
                print_syntax(child, indent + 2);
            }
        }
    }
}
