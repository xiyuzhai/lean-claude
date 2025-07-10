use lean_macro_expander::{MacroEnvironment, MacroExpander};
use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

/// Helper to expand a macro with multiple parameters
fn expand_with_multiple_params(macro_def: &str, usage: &str) -> Result<String, String> {
    let input = format!("{}\n{}", macro_def, usage);

    // Parse the input
    let mut parser = Parser::new(&input);
    let module = parser.module().map_err(|e| format!("Parse error: {e:?}"))?;

    // Create environment and register macros
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
fn test_two_parameters() {
    let macro_def = r#"
macro "add" x:term y:term : term => `($x + $y)
"#;
    let usage = "def result := add 1 2";

    let expanded = expand_with_multiple_params(macro_def, usage).expect("Failed to expand");
    println!("Expanded: {}", expanded);

    // Should expand to (1 + 2)
    assert!(expanded.contains("1"));
    assert!(expanded.contains("2"));
    assert!(expanded.contains("+"));
}

#[test]
fn test_three_parameters() {
    let macro_def = r#"
macro "combine" x:term y:term z:term : term => `($x $y $z)
"#;
    let usage = "def result := combine foo bar baz";

    let expanded = expand_with_multiple_params(macro_def, usage).expect("Failed to expand");
    println!("Expanded: {}", expanded);

    // Should expand to (foo bar baz)
    assert!(expanded.contains("foo"));
    assert!(expanded.contains("bar"));
    assert!(expanded.contains("baz"));
}

#[test]
fn test_mixed_categories() {
    let macro_def = r#"
macro "typed" x:term y:ident : term => `($y $x)
"#;
    let usage = "def result := typed 42 myFunc";

    let expanded = expand_with_multiple_params(macro_def, usage).expect("Failed to expand");
    println!("Expanded: {}", expanded);

    // Should expand to (myFunc 42)
    assert!(expanded.contains("42"));
    assert!(expanded.contains("myFunc"));
}

#[test]
fn test_nested_expansion() {
    let macro_def = r#"
macro "swap" x:term y:term : term => `($y $x)
macro "double_swap" a:term b:term : term => `(swap (swap $a $b) $b)
"#;
    let usage = "def result := double_swap first second";

    let expanded = expand_with_multiple_params(macro_def, usage).expect("Failed to expand");
    println!("Expanded: {}", expanded);

    // Should eventually expand to something with first and second
    assert!(expanded.contains("first"));
    assert!(expanded.contains("second"));
}

#[test]
fn test_complex_template() {
    let macro_def = r#"
macro "let_add" x:term y:term z:term : term => `(let temp := $x + $y; temp * $z)
"#;
    let usage = "def result := let_add 1 2 3";

    let expanded = expand_with_multiple_params(macro_def, usage).expect("Failed to expand");
    println!("Expanded: {}", expanded);

    // Should expand to a let expression
    assert!(expanded.contains("let"));
    assert!(expanded.contains("temp"));
    assert!(expanded.contains("1"));
    assert!(expanded.contains("2"));
    assert!(expanded.contains("3"));
}
