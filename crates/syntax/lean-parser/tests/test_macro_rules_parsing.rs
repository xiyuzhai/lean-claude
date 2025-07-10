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
fn test_parse_macro_rules_simple() {
    let input = "macro_rules | `(mylist []) => `(List.nil)";

    println!("Input: {input}");
    let mut parser = Parser::new(input);

    match parser.macro_rules() {
        Ok(result) => {
            println!("Success! Parsed as:");
            println!("{}", format_syntax(&result, 0));
        }
        Err(e) => {
            println!("Error parsing macro_rules: {e:?}");
        }
    }
}

#[test]
fn test_macro_rules_multiline() {
    let input = r#"macro_rules
| `(mylist []) => `(List.nil)"#;

    println!("Testing multiline macro_rules:");
    println!("Input: {input}");
    let mut parser = Parser::new(input);

    // First try as command
    match parser.command() {
        Ok(result) => {
            println!("Command parse success:");
            println!("{}", format_syntax(&result, 0));
        }
        Err(e) => {
            println!("Command parse error: {e:?}");

            // Try direct macro_rules parse
            let mut parser2 = Parser::new(input);
            match parser2.macro_rules() {
                Ok(result) => {
                    println!("Direct macro_rules parse success:");
                    println!("{}", format_syntax(&result, 0));
                }
                Err(e2) => {
                    println!("Direct macro_rules parse error: {e2:?}");
                }
            }
        }
    }
}

#[test]
fn test_parse_macro_rules_in_module() {
    let input = r#"
macro_rules
| `(mylist []) => `(List.nil)
| `(mylist [$x]) => `(List.cons $x List.nil)
"#;

    println!("Input: {input}");
    let mut parser = Parser::new(input);

    match parser.module() {
        Ok(result) => {
            println!("Module parsed successfully:");
            println!("{}", format_syntax(&result, 0));

            // Check for Error nodes
            fn has_error_nodes(syntax: &Syntax) -> bool {
                match syntax {
                    Syntax::Node(node) => {
                        if node.kind == SyntaxKind::Error {
                            return true;
                        }
                        node.children.iter().any(has_error_nodes)
                    }
                    _ => false,
                }
            }

            if has_error_nodes(&result) {
                println!("\nWARNING: Module contains Error nodes!");
            }
        }
        Err(e) => {
            println!("Error parsing module: {e:?}");
        }
    }
}

#[test]
fn test_full_macro_rules_with_defs() {
    // Test without leading newline
    let input = r#"macro_rules
| `(mylist []) => `(List.nil)
| `(mylist [$x]) => `(List.cons $x List.nil)
| `(mylist [$x, $xs,*]) => `(List.cons $x (mylist [$xs,*]))

def empty := mylist []
def single := mylist [42]
def multiple := mylist [1, 2, 3]"#;

    println!("Input: {input}");
    let mut parser = Parser::new(input);

    match parser.module() {
        Ok(result) => {
            println!("Module parsed successfully:");
            println!("{}", format_syntax(&result, 0));

            // Check for Error nodes
            fn has_error_nodes(syntax: &Syntax) -> bool {
                match syntax {
                    Syntax::Node(node) => {
                        if node.kind == SyntaxKind::Error {
                            return true;
                        }
                        node.children.iter().any(has_error_nodes)
                    }
                    _ => false,
                }
            }

            if has_error_nodes(&result) {
                println!("\nWARNING: Module contains Error nodes!");
            }
        }
        Err(e) => {
            println!("Error parsing module: {e:?}");
        }
    }
}

#[test]
fn test_just_macro_rules_in_module() {
    let input = r#"macro_rules
| `(mylist []) => `(List.nil)
| `(mylist [$x]) => `(List.cons $x List.nil)
| `(mylist [$x, $xs,*]) => `(List.cons $x (mylist [$xs,*]))"#;

    println!("Testing just macro_rules in module:");
    println!("Input: {input}");
    let mut parser = Parser::new(input);

    match parser.module() {
        Ok(result) => {
            println!("Module parsed successfully:");
            println!("{}", format_syntax(&result, 0));

            // Check for Error nodes
            fn has_error_nodes(syntax: &Syntax) -> bool {
                match syntax {
                    Syntax::Node(node) => {
                        if node.kind == SyntaxKind::Error {
                            return true;
                        }
                        node.children.iter().any(has_error_nodes)
                    }
                    _ => false,
                }
            }

            if has_error_nodes(&result) {
                println!("\nWARNING: Module contains Error nodes!");
            }
        }
        Err(e) => {
            println!("Error parsing module: {e:?}");
        }
    }
}

#[test]
fn test_macro_rules_as_command_multiline() {
    let input = r#"macro_rules
| `(mylist []) => `(List.nil)"#;

    println!("Testing macro_rules as command (multiline):");
    println!("Input: {input}");
    let mut parser = Parser::new(input);

    println!("peek(): {:?}", parser.peek());
    println!(
        "peek_keyword(\"macro_rules\"): {}",
        parser.peek_keyword("macro_rules")
    );
    println!("peek_keyword(\"macro\"): {}", parser.peek_keyword("macro"));

    match parser.command() {
        Ok(result) => {
            println!("Command parse success:");
            println!("{}", format_syntax(&result, 0));
        }
        Err(e) => {
            println!("Command parse error: {e:?}");
        }
    }
}

#[test]
fn test_minimal_failing_case() {
    // Start with the simplest case that might fail
    let inputs = vec![
        // Case 1: Just macro_rules alone
        ("macro_rules", "Just keyword"),
        // Case 2: With immediate pipe
        ("macro_rules|", "With pipe no space"),
        // Case 3: With space and pipe
        ("macro_rules |", "With space and pipe"),
        // Case 4: Newline after keyword
        ("macro_rules\n|", "Newline after keyword"),
        // Case 5: Complete minimal rule
        ("macro_rules | `(x) => `(y)", "Complete minimal"),
        // Case 6: Leading newline (like in the failing test)
        ("\nmacro_rules | `(x) => `(y)", "Leading newline"),
        // Case 7: The actual failing pattern
        (
            "\nmacro_rules\n| `(mylist []) => `(List.nil)",
            "Actual failing pattern",
        ),
    ];

    for (input, desc) in inputs {
        println!("\n{}: '{}'", desc, input.replace('\n', "\\n"));
        let mut parser = Parser::new(input);

        // Try as module
        match parser.module() {
            Ok(result) => {
                let formatted = format_syntax(&result, 0);
                if formatted.contains("Error") {
                    println!("  Module: Contains Error node!");
                    println!("  {formatted}");
                } else {
                    println!("  Module: Success (no errors)");
                }
            }
            Err(e) => {
                println!("  Module: Parse failed - {e:?}");
            }
        }
    }
}

#[test]
fn test_syntax_quotation_with_list() {
    let input = "`(mylist [])";

    println!("Input: {input}");
    let mut parser = Parser::new(input);

    match parser.parse_syntax_quotation() {
        Ok(result) => {
            println!("Success! Parsed as:");
            println!("{}", format_syntax(&result, 0));
        }
        Err(e) => {
            println!("Error parsing syntax quotation: {e:?}");
        }
    }
}

#[test]
fn test_exact_failing_input() {
    // The exact input from the failing test
    let input = r#"
macro_rules
| `(mylist []) => `(List.nil)
| `(mylist [$x]) => `(List.cons $x List.nil)
| `(mylist [$x, $xs,*]) => `(List.cons $x (mylist [$xs,*]))

def empty := mylist []
def single := mylist [42]
def multiple := mylist [1, 2, 3]
"#;

    println!("Testing exact failing input:");
    println!("First 50 chars: {:?}", &input[..50.min(input.len())]);

    let mut parser = Parser::new(input);
    match parser.module() {
        Ok(result) => {
            let formatted = format_syntax(&result, 0);
            println!("Module parsed:");
            println!("{formatted}");

            // Count the children
            if let Syntax::Node(module_node) = &result {
                println!("\nModule has {} children", module_node.children.len());
                for (i, child) in module_node.children.iter().enumerate() {
                    if let Syntax::Node(child_node) = child {
                        println!("  Child {}: {:?}", i, child_node.kind);
                    }
                }
            }

            if formatted.contains("Error") {
                println!("\nERROR NODES FOUND!");
                // Find and print error nodes
                fn find_errors(syntax: &Syntax, path: String) {
                    if let Syntax::Node(node) = syntax {
                        let node_path = format!("{}/{:?}", path, node.kind);
                        if node.kind == SyntaxKind::Error {
                            println!("  Error at: {node_path}");
                        }
                        for (i, child) in node.children.iter().enumerate() {
                            find_errors(child, format!("{node_path}[{i}]"));
                        }
                    }
                }
                find_errors(&result, "Module".to_string());
            }
        }
        Err(e) => {
            println!("Module parse failed: {e:?}");
        }
    }
}

#[test]
fn test_without_leading_newline() {
    // Same input but without the leading newline
    let input = r#"macro_rules
| `(mylist []) => `(List.nil)
| `(mylist [$x]) => `(List.cons $x List.nil)
| `(mylist [$x, $xs,*]) => `(List.cons $x (mylist [$xs,*]))

def empty := mylist []
def single := mylist [42]
def multiple := mylist [1, 2, 3]"#;

    println!("Testing without leading newline:");
    println!("First 50 chars: {:?}", &input[..50.min(input.len())]);

    let mut parser = Parser::new(input);
    match parser.module() {
        Ok(result) => {
            let formatted = format_syntax(&result, 0);

            if formatted.contains("Error") {
                println!("Still has errors!");
                println!("{formatted}");
            } else {
                println!("Success! No errors");
                // Check if macro_rules is present
                if let Syntax::Node(module_node) = &result {
                    for (i, child) in module_node.children.iter().enumerate() {
                        if let Syntax::Node(child_node) = child {
                            if child_node.kind == SyntaxKind::MacroRules {
                                println!("Found MacroRules at position {i}");
                            }
                        }
                    }
                }
            }
        }
        Err(e) => {
            println!("Module parse failed: {e:?}");
        }
    }
}
