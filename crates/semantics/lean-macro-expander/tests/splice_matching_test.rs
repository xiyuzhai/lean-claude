use eterned::BaseCoword;
use im::HashMap;
use lean_macro_expander::pattern::{substitute_template, PatternMatcher};
use lean_parser::Parser;
use lean_syn_expr::Syntax;

#[test]
#[ignore] // TODO: Advanced splice pattern matching needs more sophisticated
          // implementation
fn test_splice_pattern_matching() {
    // Test that splice patterns match correctly
    // For now, create a simpler test to isolate the issue

    // Create pattern manually: App(wrap, SyntaxSplice(xs))
    use lean_syn_expr::{SourcePos, SourceRange, SyntaxAtom, SyntaxKind, SyntaxNode};

    let dummy_range = SourceRange {
        start: SourcePos::new(0, 0, 0),
        end: SourcePos::new(0, 0, 0),
    };

    let pattern = Syntax::Node(Box::new(SyntaxNode::new(
        SyntaxKind::App,
        dummy_range,
        vec![
            Syntax::Atom(SyntaxAtom::new(
                dummy_range,
                BaseCoword::new("wrap".to_string()),
            )),
            Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::SyntaxSplice,
                dummy_range,
                vec![Syntax::Atom(SyntaxAtom::new(
                    dummy_range,
                    BaseCoword::new("xs".to_string()),
                ))]
                .into(),
            ))),
        ]
        .into(),
    )));

    // Create syntax manually: App(wrap, a, b, c)
    let syntax = Syntax::Node(Box::new(SyntaxNode::new(
        SyntaxKind::App,
        dummy_range,
        vec![
            Syntax::Atom(SyntaxAtom::new(
                dummy_range,
                BaseCoword::new("wrap".to_string()),
            )),
            Syntax::Atom(SyntaxAtom::new(
                dummy_range,
                BaseCoword::new("a".to_string()),
            )),
            Syntax::Atom(SyntaxAtom::new(
                dummy_range,
                BaseCoword::new("b".to_string()),
            )),
            Syntax::Atom(SyntaxAtom::new(
                dummy_range,
                BaseCoword::new("c".to_string()),
            )),
        ]
        .into(),
    )));

    println!("Manual pattern: {pattern:?}");
    println!("Manual syntax: {syntax:?}");

    let match_result =
        PatternMatcher::match_pattern(&pattern, &syntax).expect("Pattern matching failed");

    println!("Match result: {match_result:?}");

    assert!(match_result.is_some(), "Pattern should match");

    if let Some(pattern_match) = match_result {
        println!("Bindings: {:?}", pattern_match.bindings);
        assert!(
            pattern_match
                .bindings
                .contains_key(&BaseCoword::new("xs".to_string())),
            "Should bind xs"
        );
    }
}

#[test]
fn test_splice_template_substitution() {
    // Test that splice templates substitute correctly
    let template_str = "`(outer $xs,* inner)";

    let mut template_parser = Parser::new(template_str);
    let template = template_parser
        .parse_syntax_quotation()
        .expect("Failed to parse template");

    // Extract inner template
    let inner_template = if let Syntax::Node(node) = &template {
        node.children.first().cloned().unwrap_or(template.clone())
    } else {
        template.clone()
    };

    // Create bindings - xs should bind to a sequence
    let mut bindings = HashMap::new();

    // Parse "a b c" as a sequence
    let mut seq_parser = Parser::new("a b c");
    let a = seq_parser.identifier().unwrap();
    seq_parser.skip_whitespace();
    let b = seq_parser.identifier().unwrap();
    seq_parser.skip_whitespace();
    let c = seq_parser.identifier().unwrap();

    // Create an App node to hold the sequence
    let seq = Syntax::Node(Box::new(lean_syn_expr::SyntaxNode::new(
        lean_syn_expr::SyntaxKind::App,
        lean_syn_expr::SourceRange {
            start: lean_syn_expr::SourcePos::new(0, 0, 0),
            end: lean_syn_expr::SourcePos::new(0, 0, 0),
        },
        vec![a, b, c].into(),
    )));

    bindings.insert(BaseCoword::new("xs".to_string()), seq);

    let result =
        substitute_template(&inner_template, &bindings).expect("Template substitution failed");

    println!("Template: {inner_template:?}");
    println!("Result: {result:?}");

    // Check that the result contains the expected structure
    let result_str = format!("{result:?}");
    assert!(result_str.contains("outer"), "Should contain outer");
    assert!(result_str.contains("inner"), "Should contain inner");
    assert!(result_str.contains("a"), "Should contain a");
    assert!(result_str.contains("b"), "Should contain b");
    assert!(result_str.contains("c"), "Should contain c");
}
