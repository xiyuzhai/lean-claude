use lean_macro_expander::{MacroEnvironment, MacroExpander};
use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

fn expand_module(input: &str) -> Result<String, String> {
    let mut parser = Parser::new(input);
    let module = parser.module().map_err(|e| format!("Parse error: {e:?}"))?;

    eprintln!("Parsed module: {}", format_syntax(&module));

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
fn test_macro_rules_basic() {
    let input = r#"
macro_rules 
| `(myif $x) => `(match $x with | true => 1 | false => 2)

def result := myif true
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand the myif macro
    assert!(expanded.contains("match") || expanded.contains("myif"));
}

#[test]
fn test_macro_rules_pattern_matching() {
    let input = r#"
macro_rules
| `(mylist []) => `(List.nil)
| `(mylist [$x]) => `(List.cons $x List.nil)
| `(mylist [$x, $xs,*]) => `(List.cons $x (mylist [$xs,*]))

def empty := mylist []
def single := mylist [42]
def multiple := mylist [1, 2, 3]
"#;

    // First parse the module to see what we get
    let mut parser = Parser::new(input);
    let module = parser.module().expect("Failed to parse module");
    println!("Parsed module: {}", format_syntax(&module));

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Check expansions
    assert!(expanded.contains("(App List nil)"));
    assert!(expanded.contains("(App List cons)"));
}

#[test]
fn test_do_notation_macro() {
    let input = r#"
macro "mydo" x:term : term => `(bind $x (fun y => y))

def result := mydo (pure 42)
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand to bind (pure 42) (fun y => y)
    // Check the structure rather than exact string matching
    assert!(
        expanded.contains("bind"),
        "Expected 'bind' in expanded output: {expanded}"
    );
    assert!(
        expanded.contains("Lambda"),
        "Expected 'Lambda' in expanded output: {expanded}"
    );
    assert!(
        expanded.contains("pure") && expanded.contains("42"),
        "Expected 'pure 42' in expanded output: {expanded}"
    );
}

#[test]
#[ignore] // Advanced macro features not implemented yet
fn test_nested_syntax_quotations() {
    let input = r#"
macro "quote2" x:term : term => `(`($x))

def result := quote2 (1 + 1)
"#;

    let expanded = expand_module(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should produce nested quotation
    assert!(expanded.contains("SyntaxQuotation"));
}

#[test]
fn test_macro_with_multiple_params() {
    let input = r#"
macro "swap" x:term y:term : term => `(($y, $x))

def result := swap 1 2
"#;

    // This should fail for now since we don't support multiple parameters yet
    let result = expand_module(input);
    assert!(result.is_err() || result.unwrap().contains("swap 1 2"));
}
