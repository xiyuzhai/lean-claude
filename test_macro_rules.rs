use lean_macro_expander::{MacroEnvironment, MacroExpander};
use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

fn main() {
    let input = r#"
macro_rules 
| `(myif true then $x else $y) => `($x)
| `(myif false then $x else $y) => `($y)
| `(myif $c then $x else $y) => `(if $c then $x else $y)

def result := myif true then 1 else 2
"#;

    let mut parser = Parser::new(input);
    let module = parser.module().expect("Failed to parse");

    println!("Parsed module: {module:#?}");

    let mut env = MacroEnvironment::new();

    // Collect macro definitions
    if let Syntax::Node(module_node) = &module {
        println!("Module has {} children", module_node.children.len());
        for (i, child) in module_node.children.iter().enumerate() {
            println!("Child {i}: {:?}", child.kind());
            if let Syntax::Node(node) = child {
                if node.kind == SyntaxKind::MacroDef {
                    println!("Found macro def: {node:?}");
                    match MacroEnvironment::create_macro_from_syntax(child) {
                        Ok(macro_def) => {
                            println!("Registering macro: {}", macro_def.name);
                            env.register_macro(macro_def);
                        }
                        Err(e) => {
                            println!("Failed to create macro: {e:?}");
                        }
                    }
                } else if node.kind == SyntaxKind::MacroRules {
                    println!("Found macro_rules: {node:?}");
                    match MacroEnvironment::create_macros_from_macro_rules(child) {
                        Ok(macro_defs) => {
                            println!("Registering {} macros from macro_rules", macro_defs.len());
                            for macro_def in macro_defs {
                                println!("  Registering macro: {}", macro_def.name);
                                env.register_macro(macro_def);
                            }
                        }
                        Err(e) => {
                            println!("Failed to create macros from macro_rules: {e:?}");
                        }
                    }
                }
            }
        }
    }

    println!(
        "Environment has {} macros",
        if env.has_any_macros() { "some" } else { "no" }
    );

    let mut expander = MacroExpander::new(env);
    let expanded = expander.expand(&module).expect("Failed to expand");

    println!("Expanded: {expanded:#?}");
}