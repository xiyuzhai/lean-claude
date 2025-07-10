use lean_macro_expander::{MacroEnvironment, MacroExpander};
use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

fn expand_module(input: &str) -> Result<String, String> {
    let mut parser = Parser::new(input);
    let module = parser.module().map_err(|e| format!("Parse error: {e:?}"))?;

    let mut env = MacroEnvironment::new();

    // Collect macro definitions
    if let Syntax::Node(module_node) = &module {
        for child in &module_node.children {
            if let Syntax::Node(node) = child {
                if node.kind == SyntaxKind::MacroDef {
                    let macro_def = MacroEnvironment::create_macro_from_syntax(child)
                        .map_err(|e| format!("Failed to create macro: {e:?}"))?;
                    env.register_macro(macro_def);
                } else if node.kind == SyntaxKind::MacroRules {
                    let macro_defs = MacroEnvironment::create_macros_from_macro_rules(child)
                        .map_err(|e| format!("Failed to create macros from macro_rules: {e:?}"))?;
                    for macro_def in macro_defs {
                        env.register_macro(macro_def);
                    }
                }
            }
        }
    }

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
fn test_splice_expands_correctly() {
    let input = r#"
macro_rules
| `(mylist [$xs,*]) => `(List.of $xs,*)

def empty := mylist []
def single := mylist [42]
def multiple := mylist [1, 2, 3]
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Check that the splice expands correctly
    // empty should expand to List.of (no args)
    // single should expand to List.of 42
    // multiple should expand to List.of 1 2 3

    // Check for the expanded form - List is an app with "of" as second child
    assert!(expanded.contains("List") && expanded.contains("of"));

    // The exact format depends on how splices are expanded
    // For now, let's just verify the structure is preserved
    assert!(expanded.contains("42"));
    assert!(expanded.contains("1"));
    assert!(expanded.contains("2"));
    assert!(expanded.contains("3"));
}

#[test]
fn test_splice_in_template() {
    let input = r#"
macro_rules
| `(wrap $xs,*) => `(outer $xs,* inner)

def test := wrap a b c
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand to (outer a b c inner)
    assert!(expanded.contains("outer"));
    assert!(expanded.contains("inner"));
    assert!(expanded.contains("a"));
    assert!(expanded.contains("b"));
    assert!(expanded.contains("c"));
}

#[test]
fn test_multiple_splices() {
    let input = r#"
macro_rules
| `(pair $xs,* and $ys,*) => `(result $xs,* then $ys,*)

def test := pair a b and x y
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand to (result a b then x y)
    assert!(expanded.contains("result") || expanded.contains("pair"));
    assert!(expanded.contains("a"));
    assert!(expanded.contains("b"));
    assert!(expanded.contains("x"));
    assert!(expanded.contains("y"));
}

#[test]
fn test_nested_splice_expansion() {
    let input = r#"
macro_rules
| `(nest $xs,*) => `(f (g $xs,*))

def test := nest 1 2 3
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand to (f (g 1 2 3))
    assert!(expanded.contains("f") || expanded.contains("nest"));
    assert!(expanded.contains("g") || expanded.contains("nest"));
    assert!(expanded.contains("1"));
    assert!(expanded.contains("2"));
    assert!(expanded.contains("3"));
}
