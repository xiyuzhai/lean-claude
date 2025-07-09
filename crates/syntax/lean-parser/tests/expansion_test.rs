use lean_parser::ExpandingParser;
use lean_syn_expr::Syntax;

fn format_syntax(syntax: &Syntax) -> String {
    match syntax {
        Syntax::Missing => "<missing>".to_string(),
        Syntax::Atom(atom) => atom.value.to_string(),
        Syntax::Node(node) => {
            let kind = format!("{:?}", node.kind);
            if node.children.is_empty() {
                format!("({kind})")
            } else {
                let children: Vec<String> = node.children.iter().map(format_syntax).collect();
                format!("({} {})", kind, children.join(" "))
            }
        }
    }
}

#[test]
fn test_parser_with_macro_expansion() {
    let input = r#"
macro "twice" x:term : term => `($x + $x)
def result := twice 42
"#;

    let mut parser = ExpandingParser::new(input);
    let expanded = parser.parse_module().expect("Failed to parse and expand");

    let output = format_syntax(&expanded);
    println!("Expanded output: {}", output);

    // Check that the macro was expanded
    assert!(output.contains("(BinOp 42 + 42)"));
}

#[test]
fn test_multiple_macros_and_uses() {
    let input = r#"
macro "double" x:term : term => `($x * 2)
macro "triple" x:term : term => `($x * 3)

def a := double 5
def b := triple 7
def c := double (triple 2)
"#;

    let mut parser = ExpandingParser::new(input);
    let expanded = parser.parse_module().expect("Failed to parse and expand");

    let output = format_syntax(&expanded);
    println!("Expanded output: {}", output);

    // Check that all macros were expanded
    assert!(output.contains("(BinOp 5 * 2)"));
    assert!(output.contains("(BinOp 7 * 3)"));
    assert!(output.contains("(BinOp (BinOp 2 * 3) * 2)"));
}
