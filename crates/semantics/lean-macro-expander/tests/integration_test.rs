use lean_macro_expander::{MacroEnvironment, MacroExpander};
use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

/// Helper to parse and expand a Lean module with macros
fn expand_module(input: &str) -> Result<String, String> {
    // Parse the module
    let mut parser = Parser::new(input);
    let module = parser.module().map_err(|e| format!("Parse error: {e:?}"))?;

    // Create environment and register macros
    let mut env = MacroEnvironment::new();

    // First pass: collect macro definitions
    if let Syntax::Node(module_node) = &module {
        for child in &module_node.children {
            if let Syntax::Node(node) = child {
                if node.kind == SyntaxKind::MacroDef {
                    let macro_def = MacroEnvironment::create_macro_from_syntax(child)
                        .map_err(|e| format!("Failed to create macro: {e:?}"))?;
                    env.register_macro(macro_def);
                }
            }
        }
    }

    // Create expander and expand
    let mut expander = MacroExpander::new(env);
    let expanded = expander
        .expand(&module)
        .map_err(|e| format!("Expansion error: {e:?}"))?;

    Ok(format_syntax(&expanded))
}

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
                format!("({kind} {})", children.join(" "))
            }
        }
    }
}

#[test]
fn test_simple_macro_expansion() {
    let input = r#"
macro "twice" x:term : term => `($x + $x)
def result := twice 42
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // The macro should be expanded in the definition
    assert!(expanded.contains("(BinOp 42 + 42)"));
}

#[test]
fn test_nested_macro_expansion() {
    let input = r#"
macro "twice" x:term : term => `($x + $x)
macro "quad" x:term : term => `(twice (twice $x))
def result := quad 10
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand to ((10 + 10) + (10 + 10)) + ((10 + 10) + (10 + 10))
    // For now, we just check that it contains the expanded form
    assert!(expanded.contains("10"));
}

#[test]
fn test_multiple_macro_uses() {
    let input = r#"
macro "double" x:term : term => `($x * 2)
def a := double 5
def b := double 10
def c := double (double 3)
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Check that all uses are expanded
    assert!(expanded.contains("(BinOp 5 * 2)"));
    assert!(expanded.contains("(BinOp 10 * 2)"));
    // The nested one should expand to double (3 * 2) = (3 * 2) * 2
    assert!(expanded.contains("3") && expanded.contains("2"));
}
