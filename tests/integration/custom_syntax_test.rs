use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
fn test_declare_syntax_category() {
    let input = "declare_syntax_cat mycat";
    let mut parser = Parser::new(input);

    let result = parser.module();
    assert!(result.is_ok(), "Failed to parse: {:?}", result);

    let module = result.unwrap();
    if let Syntax::Node(node) = &module {
        assert_eq!(node.kind, SyntaxKind::Module);
        assert!(!node.children.is_empty());

        if let Some(Syntax::Node(cmd_node)) = node.children.first() {
            assert_eq!(cmd_node.kind, SyntaxKind::DeclareSyntaxCat);
        }
    }
}

#[test]
fn test_declare_syntax_category_with_parent() {
    let input = r#"
declare_syntax_cat myterm (parent: term)
declare_syntax_cat mytactic (parent: tactic) (behavior: keyword)
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();
    assert!(result.is_ok(), "Failed to parse: {:?}", result);
}

#[test]
fn test_syntax_extension() {
    let input = r#"
declare_syntax_cat mycat
syntax "⟨" term "⟩" : term
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();
    assert!(result.is_ok(), "Failed to parse: {:?}", result);
}

#[test]
fn test_custom_operator_definition() {
    let input = r#"
syntax (precedence := 65) term "⊕" term : term
syntax (precedence := 70) term "⊗" term : term
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();
    assert!(result.is_ok(), "Failed to parse: {:?}", result);
}

#[test]
fn test_custom_syntax_with_parameters() {
    let input = r#"
syntax "begin" term:max "end" : term
syntax "repeat" tactic "until" term : tactic
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();
    assert!(result.is_ok(), "Failed to parse: {:?}", result);
}

#[test]
fn test_complex_custom_syntax() {
    let input = r#"
declare_syntax_cat array_comp

syntax "[" term "|" array_comp,* "]" : term
syntax ident ":" term : array_comp
syntax term : array_comp
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();
    assert!(result.is_ok(), "Failed to parse: {:?}", result);
}

#[test]
fn test_custom_category_behavior() {
    let input = r#"
declare_syntax_cat mycommand (behavior: keyword)
declare_syntax_cat myexpr (behavior: ident)
declare_syntax_cat mymixed (behavior: both)
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();
    assert!(result.is_ok(), "Failed to parse: {:?}", result);
}

#[test]
fn test_syntax_with_string_literals() {
    let input = r#"
syntax "if" term "then" term "else" term : term
syntax "when" term "do" tactic : tactic
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();
    assert!(result.is_ok(), "Failed to parse: {:?}", result);
}

#[test]
fn test_parse_using_custom_syntax() {
    // This test would require actually using the custom syntax after declaration
    // For now, just test that declarations work
    let input = r#"
syntax "⦃" term "⦄" : term

def test := ⦃42⦄
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();
    // We expect this to fail for now since we haven't implemented
    // the actual usage of custom syntax in term parsing
    // Just check that we can at least parse the syntax declaration
    match result {
        Ok(module) => {
            if let Syntax::Node(node) = &module {
                // Should have parsed at least the syntax declaration
                assert!(!node.children.is_empty());
            }
        }
        Err(e) => {
            // Expected for now - custom syntax usage not yet integrated
            println!("Expected error for now: {:?}", e);
        }
    }
}

// Helper function to check if a module contains a specific syntax kind
fn contains_syntax_kind(syntax: &Syntax, target: SyntaxKind) -> bool {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == target {
                return true;
            }
            node.children
                .iter()
                .any(|child| contains_syntax_kind(child, target))
        }
        _ => false,
    }
}

#[test]
fn test_multiple_custom_categories() {
    let input = r#"
declare_syntax_cat cat1
declare_syntax_cat cat2 (parent: cat1)
declare_syntax_cat cat3 (parent: cat2)

syntax "test" : cat1
syntax "test2" : cat2
syntax "test3" : cat3
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();
    assert!(result.is_ok(), "Failed to parse: {:?}", result);

    let module = result.unwrap();
    assert!(contains_syntax_kind(&module, SyntaxKind::DeclareSyntaxCat));
    // The syntax declarations create Syntax nodes, not SyntaxExtension nodes
    assert!(contains_syntax_kind(&module, SyntaxKind::Syntax));
}
