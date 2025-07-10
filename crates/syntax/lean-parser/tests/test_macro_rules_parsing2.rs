use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

fn format_syntax(syntax: &Syntax, indent: usize) -> String {
    let prefix = " ".repeat(indent);
    match syntax {
        Syntax::Missing => format!("{prefix}<missing>"),
        Syntax::Atom(atom) => format!("{}Atom('{}')", prefix, atom.value),
        Syntax::Node(node) => {
            let mut result = format!("{}Node({:?}):", prefix, node.kind);
            if node.kind == SyntaxKind::Error {
                result.push_str(" <ERROR>");
            }
            for child in &node.children {
                result.push('\n');
                result.push_str(&format_syntax(child, indent + 2));
            }
            result
        }
    }
}

#[test]
fn test_macro_rules_without_splice() {
    // Test without the splice pattern that uses ,*
    let input = r#"macro_rules
| `(mylist []) => `(List.nil)
| `(mylist [$x]) => `(List.cons $x List.nil)

def empty := mylist []
def single := mylist [42]"#;

    println!("Testing without splice pattern:");
    let mut parser = Parser::new(input);
    match parser.module() {
        Ok(result) => {
            let formatted = format_syntax(&result, 0);
            if formatted.contains("Error") {
                println!("Has errors:");
                println!("{formatted}");
            } else {
                println!("Success! No errors");
                // Count MacroRules
                if let Syntax::Node(module_node) = &result {
                    let macro_rules_count = module_node.children.iter().filter(|child| {
                        matches!(child, Syntax::Node(n) if n.kind == SyntaxKind::MacroRules)
                    }).count();
                    println!("Found {macro_rules_count} MacroRules nodes");
                }
            }
        }
        Err(e) => {
            println!("Module parse failed: {e:?}");
        }
    }
}

#[test]
fn test_just_macro_rules_splice() {
    // Test just the macro_rules with splice, no defs
    let input = r#"macro_rules
| `(mylist []) => `(List.nil)
| `(mylist [$x]) => `(List.cons $x List.nil)
| `(mylist [$x, $xs,*]) => `(List.cons $x (mylist [$xs,*]))"#;

    println!("Testing just macro_rules with splice:");
    let mut parser = Parser::new(input);
    match parser.module() {
        Ok(result) => {
            let formatted = format_syntax(&result, 0);
            if formatted.contains("Error") {
                println!("Has errors:");
                println!("{formatted}");
            } else {
                println!("Success! No errors");
            }
        }
        Err(e) => {
            println!("Module parse failed: {e:?}");
        }
    }
}
