use lean_parser::Parser;
use lean_syn_expr::Syntax;

#[test]
fn test_method_calls() {
    let test_cases = vec![
        ("xs.reverse", "method call without args"),
        ("list.map f", "method call with single arg"),
        ("list.foldl add 0", "method call with multiple args"),
        ("x.field", "field projection"),
        ("x.1", "numeric projection"),
        ("x.field.subfield", "chained projections"),
        ("xs.reverse.head", "method call then projection"),
    ];

    for (input, description) in test_cases {
        println!("\nTesting: {input} - {description}");
        let mut parser = Parser::new(input);
        match parser.term() {
            Ok(syntax) => {
                println!("✓ Parsed successfully");
                print_syntax(&syntax, 0);
            }
            Err(e) => {
                println!("✗ Parse error: {e:?}");
            }
        }
    }
}

#[test]
fn test_method_calls_in_context() {
    let test_cases = vec![
        ("for x in xs.reverse do body", "method call in for loop"),
        ("def test := xs.reverse.head", "method call in definition"),
        (
            "let ys := list.map (fun x => x + 1)",
            "method call with lambda arg",
        ),
    ];

    for (input, description) in test_cases {
        println!("\nTesting: {input} - {description}");
        let mut parser = Parser::new(input);
        match parser.module() {
            Ok(syntax) => {
                println!("✓ Parsed successfully");
                print_syntax(&syntax, 0);
            }
            Err(e) => {
                println!("✗ Parse error: {e:?}");
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
