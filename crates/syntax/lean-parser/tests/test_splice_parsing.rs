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
fn test_parse_splice_in_quotation() {
    // Test parsing a splice in a syntax quotation
    let input = "`(mylist [$xs,*])";

    println!("Testing splice in quotation: {input}");
    let mut parser = Parser::new(input);

    match parser.parse_syntax_quotation() {
        Ok(result) => {
            println!("Success!");
            println!("{}", format_syntax(&result, 0));
        }
        Err(e) => {
            println!("Error: {e:?}");
        }
    }
}

#[test]
fn test_parse_macro_rule_with_splice() {
    // Test a single macro rule with splice
    let input = "macro_rules | `(mylist [$x, $xs,*]) => `(List.cons $x (mylist [$xs,*]))";

    println!("Testing single macro rule with splice:");
    let mut parser = Parser::new(input);

    match parser.macro_rules() {
        Ok(result) => {
            println!("Success!");
            println!("{}", format_syntax(&result, 0));
        }
        Err(e) => {
            println!("Error: {e:?}");
        }
    }
}

#[test]
fn test_parse_splice_patterns() {
    let patterns = vec!["$xs,*", "[$xs,*]", "($xs,*)", "$x, $xs,*"];

    for pattern in patterns {
        println!("\nTesting pattern in quotation: `({pattern})");
        let input = format!("`({pattern})");
        let mut parser = Parser::new(&input);

        match parser.parse_syntax_quotation() {
            Ok(result) => {
                println!("  Success!");
                // Check if it contains a splice
                fn has_splice(syntax: &Syntax) -> bool {
                    match syntax {
                        Syntax::Node(node) => {
                            node.kind == SyntaxKind::SyntaxSplice
                                || node.children.iter().any(has_splice)
                        }
                        _ => false,
                    }
                }

                if has_splice(&result) {
                    println!("  Contains splice node ✓");
                } else {
                    println!("  Warning: No splice node found!");
                }
            }
            Err(e) => {
                println!("  Error: {e:?}");
            }
        }
    }
}

#[test]
fn test_nested_parens_in_quotation() {
    // Test nested parentheses without splice first
    let inputs = vec![
        ("`(a (b))", "simple nested"),
        ("`(List.cons x y)", "simple cons"),
        ("`(List.cons $x y)", "cons with antiquot"),
        ("`(List.cons $x (f y))", "cons with nested call"),
        ("`(List.cons $x (mylist []))", "cons with mylist"),
        ("`(List.cons $x (mylist [$xs,*]))", "cons with splice"),
    ];

    for (input, desc) in inputs {
        println!("\nTesting {desc}: {input}");
        let mut parser = Parser::new(input);

        match parser.parse_syntax_quotation() {
            Ok(_result) => {
                println!("  Success!");
            }
            Err(e) => {
                println!("  Error at position {}: {:?}", e.position.offset, e.kind);
            }
        }
    }
}
