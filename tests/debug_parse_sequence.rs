#![allow(clippy::uninlined_format_args)]

#[test]
fn debug_parse_sequence() {
    use lean_parser::Parser;
    use lean_syn_expr::Syntax;

    // Test just structure followed by inductive
    let input = r#"structure Point where
  x : Nat
  y : Nat

inductive Color where
  | red | green | blue"#;

    println!("=== Testing Structure + Inductive ===");
    println!("Input:\n{}", input);

    let mut parser = Parser::new(input);
    let module = parser.module();

    match module {
        Ok(Syntax::Node(node)) => {
            println!("\nModule parsed with {} commands", node.children.len());
            for (i, child) in node.children.iter().enumerate() {
                match child {
                    Syntax::Node(n) => {
                        println!("  Command {}: {:?}", i, n.kind);
                        if n.kind == lean_syn_expr::SyntaxKind::Error {
                            println!("    Error range: {:?}", n.range);
                        }
                    }
                    _ => println!("  Command {}: Not a node", i),
                }
            }
        }
        Ok(_) => println!("Not a module node"),
        Err(e) => println!("Parse error: {:?}", e),
    }

    // Now test parsing them individually
    println!("\n=== Parsing individually ===");

    let structure = "structure Point where\n  x : Nat\n  y : Nat";
    let mut p1 = Parser::new(structure);
    match p1.command() {
        Ok(_) => println!("Structure: OK"),
        Err(e) => println!("Structure: Error - {:?}", e),
    }

    let inductive = "inductive Color where\n  | red | green | blue";
    let mut p2 = Parser::new(inductive);
    match p2.command() {
        Ok(_) => println!("Inductive: OK"),
        Err(e) => println!("Inductive: Error - {:?}", e),
    }
}
