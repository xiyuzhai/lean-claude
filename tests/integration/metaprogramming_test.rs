#![allow(clippy::uninlined_format_args)]

use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
fn test_syntax_quotations() {
    let test_cases = vec![
        // Basic syntax quotation
        ("`(term| x + y)", "basic term quotation"),
        // Quotation without category
        ("`(x + y)", "implicit term quotation"),
        // Quotation with antiquotation
        ("`($x + $y)", "quotation with antiquotations"),
        // Complex quotation
        ("`(fun x => $body)", "lambda quotation with antiquotation"),
        // Quotation with typed antiquotation
        ("`($x:ident + $y:term)", "typed antiquotations"),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.term();

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}: {:#?}", description, syntax);
                assert!(
                    contains_syntax_kind(&syntax, SyntaxKind::SyntaxQuotation),
                    "Should contain syntax quotation for {}",
                    description
                );
            }
            Err(e) => panic!("Failed to parse {}: {:?}", description, e),
        }
    }
}

#[test]
fn test_antiquotations() {
    let test_cases = vec![
        // Simple antiquotation
        ("$x", "simple antiquotation"),
        // Parenthesized antiquotation
        ("$(foo bar)", "parenthesized antiquotation"),
        // Typed antiquotation
        ("$x:term", "typed antiquotation"),
        // TODO: Splice antiquotations are not yet implemented
        // // Splice antiquotation
        // (
        //     "$[$xs]*",
        //     "splice antiquotation",
        // ),
        // // Splice with separator
        // (
        //     "$[$xs],*",
        //     "splice with separator",
        // ),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.term();

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}: {:#?}", description, syntax);
                assert!(
                    contains_syntax_kind(&syntax, SyntaxKind::SyntaxAntiquotation)
                        || contains_syntax_kind(&syntax, SyntaxKind::SyntaxSplice),
                    "Should contain antiquotation or splice for {}",
                    description
                );
            }
            Err(e) => panic!("Failed to parse {}: {:?}", description, e),
        }
    }
}

// TODO: Macro with quotations in expansion is not yet fully supported
// #[test]
// fn test_macro_with_quotations() {
//     let input = r#"macro "mylet" x:ident ":=" v:term : term => `(let $x :=
// $v; $x)"#;
//
//     let mut parser = Parser::new(input);
//     let result = parser.command();
//
//     match &result {
//         Ok(_) => {},
//         Err(e) => panic!("Failed to parse macro with quotations: {:?}", e),
//     }
//     let syntax = result.unwrap();
//     assert!(contains_syntax_kind(&syntax, SyntaxKind::Macro), "Should be a
// macro");     assert!(
//         contains_syntax_kind(&syntax, SyntaxKind::SyntaxQuotation),
//         "Should contain syntax quotation"
//     );
// }

// TODO: Elab with quotations has parsing issues
// #[test]
// fn test_elab_with_quotations() {
//     let input = r#"elab "myliteral" n:num : term => `($n + 1)"#;
//
//     let mut parser = Parser::new(input);
//     let result = parser.command();
//
//     match &result {
//         Ok(_) => {}
//         Err(e) => panic!("Failed to parse elab with quotations: {:?}", e),
//     }
//     let syntax = result.unwrap();
//     assert!(
//         contains_syntax_kind(&syntax, SyntaxKind::Elab),
//         "Should be an elab"
//     );
//     assert!(
//         contains_syntax_kind(&syntax, SyntaxKind::SyntaxQuotation),
//         "Should contain syntax quotation"
//     );
// }

#[test]
fn test_macro_rules_with_quotations() {
    let input = r#"macro_rules
  | `(term| myterm $x) => `($x + 1)
  | `(term| myterm $x $y) => `($x + $y)"#;

    let mut parser = Parser::new(input);
    let result = parser.command();

    assert!(result.is_ok(), "Should parse macro_rules with quotations");
    let syntax = result.unwrap();
    assert!(
        contains_syntax_kind(&syntax, SyntaxKind::MacroRules),
        "Should be macro_rules"
    );
    // Should have multiple quotations - patterns and expansions
    let quotation_count = count_syntax_kind(&syntax, SyntaxKind::SyntaxQuotation);
    assert!(
        quotation_count >= 4,
        "Should have at least 4 syntax quotations, found {}",
        quotation_count
    );
}

// TODO: Nested quotations are not yet supported
// #[test]
// fn test_nested_quotations() {
//     let input = "`(`($x + $y))";
//
//     let mut parser = Parser::new(input);
//     let result = parser.term();
//
//     match &result {
//         Ok(_) => {},
//         Err(e) => panic!("Failed to parse nested quotations: {:?}", e),
//     }
//     let syntax = result.unwrap();
//     let quotation_count = count_syntax_kind(&syntax,
// SyntaxKind::SyntaxQuotation);     assert_eq!(quotation_count, 2, "Should have
// exactly 2 nested quotations"); }

// TODO: Match with quotations has parsing issues
// #[test]
// fn test_quotation_in_match() {
//     let input = r#"match stx with
//   | `($x + $y) => `($y + $x)
//   | _ => stx"#;
//
//     let mut parser = Parser::new(input);
//     let result = parser.term();
//
//     assert!(result.is_ok(), "Should parse match with quotations");
//     let syntax = result.unwrap();
//     assert!(
//         contains_syntax_kind(&syntax, SyntaxKind::Match),
//         "Should be a match"
//     );
//     assert!(
//         contains_syntax_kind(&syntax, SyntaxKind::SyntaxQuotation),
//         "Should contain syntax quotations"
//     );
// }

// TODO: Complex elaborator with do notation has parsing issues
// #[test]
// fn test_elaborator_attributes() {
//     let input = r#"@[term_elab myElab]
// def elabMyTerm : TermElab := fun stx => do
//   match stx with
//   | `($x + $y) => do
//     let x' ← elabTerm x none
//     let y' ← elabTerm y none
//     mkAppM ``HAdd.hAdd #[x', y']
//   | _ => throwUnsupportedSyntax"#;
//
//     let mut parser = Parser::new(input);
//     let result = parser.command();
//
//     assert!(result.is_ok(), "Should parse elaborator with attributes");
//     let syntax = result.unwrap();
//     assert!(
//         contains_syntax_kind(&syntax, SyntaxKind::Def),
//         "Should be a def"
//     );
//     assert!(
//         contains_syntax_kind(&syntax, SyntaxKind::Attribute),
//         "Should have attributes"
//     );
// }

// Helper functions
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

fn count_syntax_kind(syntax: &Syntax, kind: SyntaxKind) -> usize {
    match syntax {
        Syntax::Node(node) => {
            let mut count = if node.kind == kind { 1 } else { 0 };
            for child in &node.children {
                count += count_syntax_kind(child, kind);
            }
            count
        }
        _ => 0,
    }
}
