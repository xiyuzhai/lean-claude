#![allow(clippy::uninlined_format_args)]

use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
fn test_basic_syntax_quotation() {
    // Test just the quotation syntax
    let input = "`(x + y)";

    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(
        result.is_ok(),
        "Should parse basic quotation: {:?}",
        result.err()
    );
    let syntax = result.unwrap();
    assert!(contains_syntax_kind(&syntax, SyntaxKind::SyntaxQuotation));
}

#[test]
fn test_quotation_with_category() {
    let input = "`(term| x + y)";

    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(
        result.is_ok(),
        "Should parse quotation with category: {:?}",
        result.err()
    );
    let syntax = result.unwrap();
    assert!(contains_syntax_kind(&syntax, SyntaxKind::SyntaxQuotation));
}

#[test]
fn test_simple_antiquotation() {
    let input = "$x";

    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(
        result.is_ok(),
        "Should parse simple antiquotation: {:?}",
        result.err()
    );
    let syntax = result.unwrap();
    assert!(contains_syntax_kind(
        &syntax,
        SyntaxKind::SyntaxAntiquotation
    ));
}

#[test]
fn test_quotation_with_antiquotation() {
    let input = "`($x)";

    let mut parser = Parser::new(input);
    let result = parser.term();

    assert!(
        result.is_ok(),
        "Should parse quotation with antiquotation: {:?}",
        result.err()
    );
    let syntax = result.unwrap();
    assert!(contains_syntax_kind(&syntax, SyntaxKind::SyntaxQuotation));
    assert!(contains_syntax_kind(
        &syntax,
        SyntaxKind::SyntaxAntiquotation
    ));
}

#[test]
fn test_macro_rules_basic() {
    // Test basic macro_rules syntax
    let input = r#"macro_rules
  | `(myterm) => `(42)"#;

    let mut parser = Parser::new(input);
    let result = parser.command();

    assert!(
        result.is_ok(),
        "Should parse basic macro_rules: {:?}",
        result.err()
    );
}

// Helper function
fn contains_syntax_kind(syntax: &Syntax, kind: SyntaxKind) -> bool {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == kind {
                return true;
            }
            node.children
                .iter()
                .any(|child| contains_syntax_kind(child, kind))
        }
        _ => false,
    }
}
