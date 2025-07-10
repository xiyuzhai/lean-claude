#[test]
fn debug_commands() {
    test_individual_commands();
    test_full_module();
}

fn test_individual_commands() {
    use lean_parser::Parser;
    use lean_syn_expr::Syntax;

    // Test each command separately
    let commands = vec![
        ("structure Point where\n  x : Nat\n  y : Nat", "Structure"),
        ("inductive Color where\n  | red | green | blue", "Inductive"),
        (
            "class HasColor (α : Type) where\n  getColor : α → Color",
            "Class",
        ),
        (
            "structure ColoredPoint extends Point where\n  color : Color",
            "Structure with extends",
        ),
        (
            "instance : HasColor ColoredPoint where\n  getColor p := p.color",
            "Instance",
        ),
        ("abbrev Origin := ColoredPoint.mk 0 0 Color.red", "Abbrev"),
    ];

    for (input, desc) in commands {
        println!("\n=== Testing: {desc} ===");
        println!("Input: {}", input.replace('\n', "\\n"));

        let mut parser = Parser::new(input);
        let result = parser.command();

        match result {
            Ok(cmd) => {
                println!("✓ Parsed successfully");
                match &cmd {
                    Syntax::Node(n) => println!("  Kind: {:?}", n.kind),
                    _ => println!("  Not a node"),
                }
            }
            Err(e) => {
                println!("✗ Parse error: {e:?}");
                // Debug: Show position in input
                let offset = e.position.offset;
                if offset < input.len() {
                    println!(
                        "  Error at offset {}: '{}'",
                        offset,
                        &input[offset..].chars().take(10).collect::<String>()
                    );
                }
            }
        }
    }
}

fn test_full_module() {
    use lean_parser::Parser;
    use lean_syn_expr::{Syntax, SyntaxKind};

    println!("\n\n=== Testing Full Module ===");
    let input = r#"
structure Point where
  x : Nat
  y : Nat

inductive Color where
  | red | green | blue

class HasColor (α : Type) where
  getColor : α → Color

structure ColoredPoint extends Point where
  color : Color

instance : HasColor ColoredPoint where
  getColor p := p.color

abbrev Origin := ColoredPoint.mk 0 0 Color.red
"#;

    // Test parsing each part sequentially
    println!("\n--- Testing sequential parsing ---");
    let lines: Vec<&str> = input.lines().collect();
    let mut current_input = String::new();
    let mut last_good = String::new();

    for (i, line) in lines.iter().enumerate() {
        current_input.push_str(line);
        current_input.push('\n');

        // Skip empty lines at the beginning
        if line.trim().is_empty() && current_input.trim().is_empty() {
            continue;
        }

        let mut parser = Parser::new(&current_input);
        match parser.module() {
            Ok(module) => {
                match &module {
                    Syntax::Node(node) if node.kind == SyntaxKind::Module => {
                        println!("  Line {}: OK, {} commands", i + 1, node.children.len());
                        if node
                            .children
                            .iter()
                            .any(|c| matches!(c, Syntax::Node(n) if n.kind == SyntaxKind::Error))
                        {
                            println!("    Warning: Contains error nodes");
                            // Print the specific line that caused issues
                            if !last_good.is_empty() {
                                let diff_start = last_good.len();
                                println!(
                                    "    New content: {:?}",
                                    &current_input[diff_start..].trim()
                                );
                            }
                        } else {
                            last_good = current_input.clone();
                        }
                    }
                    _ => println!("  Line {}: Not a module", i + 1),
                }
            }
            Err(e) => {
                println!("  Line {}: Parse error - {:?}", i + 1, e.kind);
                println!("    Content so far: {:?}", current_input.trim());
                break;
            }
        }
    }

    // Full parse
    println!("\n--- Full module parse ---");
    let mut parser = Parser::new(input);
    let result = parser.module();

    match result {
        Ok(module) => {
            println!("✓ Module parsed successfully");
            match &module {
                Syntax::Node(node) if node.kind == SyntaxKind::Module => {
                    println!("  Commands found: {}", node.children.len());
                    for (i, child) in node.children.iter().enumerate() {
                        match child {
                            Syntax::Node(n) => {
                                println!("    Command {}: {:?}", i, n.kind);
                                if n.kind == SyntaxKind::Error {
                                    // Try to show what content this error node covers
                                    println!("      Error node range: {:?}", n.range);
                                }
                            }
                            _ => println!("    Command {i}: Not a node"),
                        }
                    }
                }
                _ => println!("  Not a module node"),
            }
        }
        Err(e) => {
            println!("✗ Module parse error: {e:?}");
        }
    }
}
