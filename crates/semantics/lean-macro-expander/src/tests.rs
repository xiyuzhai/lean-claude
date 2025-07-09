use expect_test::{expect, Expect};
use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

use crate::{environment::MacroEnvironment, expander::MacroExpander};

fn check_expansion(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let module = parser.module().expect("Failed to parse");

    let env = MacroEnvironment::new();
    let mut expander = MacroExpander::new(env);

    match expander.expand(&module) {
        Ok(expanded) => {
            let output = format_syntax(&expanded);
            expected.assert_eq(&output);
        }
        Err(e) => {
            expected.assert_eq(&format!("Error: {e}"));
        }
    }
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
                let children: Vec<String> = node
                    .children
                    .iter()
                    .filter(|child| {
                        // Filter out whitespace and comments for cleaner output
                        match child {
                            Syntax::Node(n) => {
                                n.kind != SyntaxKind::Whitespace && n.kind != SyntaxKind::Comment
                            }
                            _ => true,
                        }
                    })
                    .map(format_syntax)
                    .collect();
                if children.is_empty() {
                    format!("({kind})")
                } else {
                    format!("({} {})", kind, children.join(" "))
                }
            }
        }
    }
}

#[test]
fn test_no_macros() {
    check_expansion("def foo := 42", expect![[r#"(Module (Def foo 42))"#]]);
}

#[test]
fn test_parse_quotation() {
    let input = r#"`($x + $x)"#;

    let mut parser = Parser::new(input);

    // Try parsing syntax quotation directly
    match parser.parse_syntax_quotation() {
        Ok(quot) => {
            println!("Parsed quotation: {}", format_syntax(&quot));
        }
        Err(e) => {
            // Let's debug what happens
            println!("Failed to parse quotation: {e:?}");

            // Try parsing the individual pieces
            let mut parser2 = Parser::new("$x");
            match parser2.parse_antiquotation() {
                Ok(ant) => println!("Antiquotation parsed: {}", format_syntax(&ant)),
                Err(e2) => println!("Failed to parse antiquotation: {e2:?}"),
            }
        }
    }
}

#[test]
fn test_simple_macro_registration() {
    let input = r#"macro "twice" x:term : term => `($x + $x)"#;

    let mut parser = Parser::new(input);

    // Try parsing just the macro command
    let macro_cmd = parser.command().expect("Failed to parse macro command");
    println!("Parsed macro command: {}", format_syntax(&macro_cmd));

    // Extract macro definition and register it
    let mut env = MacroEnvironment::new();

    if let Syntax::Node(node) = &macro_cmd {
        if node.kind == SyntaxKind::MacroDef {
            println!("Found MacroDef with {} children", node.children.len());
            for (i, c) in node.children.iter().enumerate() {
                println!("  Child {}: {}", i, format_syntax(c));
            }
            let macro_def = MacroEnvironment::create_macro_from_syntax(&macro_cmd)
                .expect("Failed to create macro");
            env.register_macro(macro_def);
        }
    }

    assert!(env.has_macro("twice"));
}

#[test]
fn test_pattern_matching() {
    use eterned::BaseCoword;
    use lean_syn_expr::{SourcePos, SourceRange, SyntaxAtom, SyntaxNode};
    use smallvec::smallvec;

    use crate::pattern::PatternMatcher;

    let dummy_range = SourceRange {
        start: SourcePos::new(0, 0, 0),
        end: SourcePos::new(0, 0, 0),
    };

    // Pattern: $x
    let pattern = Syntax::Node(Box::new(SyntaxNode {
        kind: SyntaxKind::SyntaxAntiquotation,
        range: dummy_range,
        children: smallvec![Syntax::Atom(SyntaxAtom {
            range: dummy_range,
            value: BaseCoword::new("x"),
        })],
    }));

    // Syntax: 42
    let syntax = Syntax::Atom(SyntaxAtom {
        range: dummy_range,
        value: BaseCoword::new("42"),
    });

    let result = PatternMatcher::match_pattern(&pattern, &syntax).unwrap();
    assert!(result.is_some());

    let bindings = result.unwrap().bindings;
    assert_eq!(bindings.len(), 1);
    assert!(bindings.contains_key(&BaseCoword::new("x")));
}

#[test]
fn test_template_substitution() {
    use eterned::BaseCoword;
    use im::HashMap;
    use lean_syn_expr::{SourcePos, SourceRange, SyntaxAtom, SyntaxNode};
    use smallvec::smallvec;

    use crate::pattern::substitute_template;

    let dummy_range = SourceRange {
        start: SourcePos::new(0, 0, 0),
        end: SourcePos::new(0, 0, 0),
    };

    // Template: $x + $x
    let template = Syntax::Node(Box::new(SyntaxNode {
        kind: SyntaxKind::BinOp,
        range: dummy_range,
        children: smallvec![
            Syntax::Atom(SyntaxAtom {
                range: dummy_range,
                value: BaseCoword::new("+"),
            }),
            Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::SyntaxAntiquotation,
                range: dummy_range,
                children: smallvec![Syntax::Atom(SyntaxAtom {
                    range: dummy_range,
                    value: BaseCoword::new("x"),
                })],
            })),
            Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::SyntaxAntiquotation,
                range: dummy_range,
                children: smallvec![Syntax::Atom(SyntaxAtom {
                    range: dummy_range,
                    value: BaseCoword::new("x"),
                })],
            })),
        ],
    }));

    // Bindings: x -> 42
    let mut bindings = HashMap::new();
    bindings.insert(
        BaseCoword::new("x"),
        Syntax::Atom(SyntaxAtom {
            range: dummy_range,
            value: BaseCoword::new("42"),
        }),
    );

    let result = substitute_template(&template, &bindings).unwrap();
    let formatted = format_syntax(&result);
    assert_eq!(formatted, "(BinOp + 42 42)");
}

#[test]
fn test_hygiene() {
    use crate::hygiene::NameGenerator;

    let gen = NameGenerator::new();
    let name1 = gen.fresh_name("x");
    let name2 = gen.fresh_name("x");

    assert_ne!(name1, name2);
    assert!(name1.as_str().starts_with("x."));
    assert!(name2.as_str().starts_with("x."));
}

#[test]
fn test_parse_multiple_commands() {
    let input = r#"def x := 1
def y := 2"#;

    let mut parser = Parser::new(input);

    // Try parsing individual commands first
    let mut parser2 = Parser::new("def x := 1");
    match parser2.command() {
        Ok(cmd) => println!("Single command parsed: {}", format_syntax(&cmd)),
        Err(e) => println!("Failed to parse single command: {e:?}"),
    }

    let module = parser.module().expect("Failed to parse module");

    if let Syntax::Node(module_node) = &module {
        println!("Module has {} children", module_node.children.len());
        for (i, child) in module_node.children.iter().enumerate() {
            println!("  Child {}: {}", i, format_syntax(child));
        }
        assert_eq!(module_node.children.len(), 2, "Should have 2 commands");
    }
}

#[test]
fn test_macro_expansion() {
    // Define and use a macro
    let input = r#"macro "twice" x:term : term => `($x + $x)
def foo := twice 5"#;

    let mut parser = Parser::new(input);
    let module = parser.module().expect("Failed to parse module");

    // Create environment and register macros
    let mut env = MacroEnvironment::new();

    // First pass: collect macro definitions
    if let Syntax::Node(module_node) = &module {
        for child in &module_node.children {
            if let Syntax::Node(node) = child {
                if node.kind == SyntaxKind::MacroDef {
                    let macro_def = MacroEnvironment::create_macro_from_syntax(child)
                        .expect("Failed to create macro");
                    env.register_macro(macro_def);
                }
            }
        }
    }

    // Create expander
    let mut expander = MacroExpander::new(env);

    // Debug: print the parsed module
    println!("Parsed module: {}", format_syntax(&module));
    if let Syntax::Node(module_node) = &module {
        println!("Module has {} children", module_node.children.len());
        for (i, child) in module_node.children.iter().enumerate() {
            println!("  Child {}: {}", i, format_syntax(child));
        }
    }

    // Expand the module
    match expander.expand(&module) {
        Ok(expanded) => {
            let output = format_syntax(&expanded);
            println!("Expanded module: {output}");

            // Check if macro was expanded in the definition
            assert!(output.contains("5 + 5") || output.contains("(BinOp") && output.contains("5"));
        }
        Err(e) => {
            panic!("Expansion failed: {e:?}");
        }
    }
}
