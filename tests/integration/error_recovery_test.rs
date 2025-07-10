use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
fn test_basic_error_recovery() {
    // Test recovery from missing closing parenthesis
    let input = "def foo (x : Nat := 42";
    let mut parser = Parser::new(input);

    let result = parser.module();
    // Should not panic, but return an error or recovered syntax
    assert!(result.is_ok() || result.is_err());

    // Check that we collected errors
    assert!(!parser.errors().is_empty(), "Should have recorded errors");
}

#[test]
fn test_skip_to_next_statement() {
    // Test recovery by skipping to next statement
    let input = r#"
def foo (x : Nat := garbage syntax here

def bar : Nat := 42
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();

    // Should parse at least one valid definition
    if let Ok(syntax) = result {
        let mut def_count = 0;
        count_definitions(&syntax, &mut def_count);
        assert!(
            def_count >= 1,
            "Should have recovered and parsed at least one definition"
        );
    }
}

#[test]
fn test_delimiter_recovery() {
    // Test recovery with mismatched delimiters
    let input = r#"
def foo : List Nat := [1, 2, garbage, 4]

def bar : Nat := 42
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();

    // Should recover and continue parsing
    assert!(result.is_ok() || !parser.errors().is_empty());
}

#[test]
fn test_multiple_errors() {
    // Test handling multiple errors
    let input = r#"
def foo (x : := 42  -- missing type
def bar y : Nat := y  -- missing parentheses
theorem baz := sorry  -- missing type
"#;

    let mut parser = Parser::new(input);
    let _result = parser.module();

    // Should collect multiple errors
    assert!(parser.errors().len() >= 2, "Should record multiple errors");
}

#[test]
fn test_error_limit() {
    // Test that parser stops after too many errors
    let mut bad_input = String::new();

    // Generate many syntax errors
    for i in 0..150 {
        bad_input.push_str(&format!("def bad{} (x : := {}\n", i, i));
    }

    let mut parser = Parser::new(&bad_input);
    let _result = parser.module();

    // Should stop at error limit (100 by default)
    assert!(parser.errors().len() <= 100, "Should respect error limit");
}

#[test]
fn test_recovery_in_nested_structures() {
    // Test recovery in nested contexts
    let input = r#"
structure Foo where
  x : Nat
  y : missing_type_here
  z : Int

inductive Bar
  | mk : Nat → garbage → Bar
  | other : Int → Bar
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();

    // Should still parse some structure
    if let Ok(syntax) = result {
        let mut struct_count = 0;
        let mut inductive_count = 0;
        count_structures(&syntax, &mut struct_count, &mut inductive_count);
        assert!(
            struct_count >= 1 || inductive_count >= 1,
            "Should recover and parse at least one structure"
        );
    }
}

#[test]
fn test_synchronization_points() {
    // Test that parser synchronizes at known good points
    let input = r#"
namespace Foo
  def x := garbage syntax
end Foo

namespace Bar
  def y := 42
end Bar
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();

    // Should parse both namespaces
    if let Ok(syntax) = result {
        let mut namespace_count = 0;
        count_namespaces(&syntax, &mut namespace_count);
        assert_eq!(namespace_count, 2, "Should parse both namespaces");
    }
}

// Helper functions
fn count_definitions(syntax: &Syntax, count: &mut usize) {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == SyntaxKind::Def {
                *count += 1;
            }
            for child in &node.children {
                count_definitions(child, count);
            }
        }
        _ => {}
    }
}

fn count_structures(syntax: &Syntax, struct_count: &mut usize, inductive_count: &mut usize) {
    match syntax {
        Syntax::Node(node) => {
            match node.kind {
                SyntaxKind::Structure => *struct_count += 1,
                SyntaxKind::Inductive => *inductive_count += 1,
                _ => {}
            }
            for child in &node.children {
                count_structures(child, struct_count, inductive_count);
            }
        }
        _ => {}
    }
}

fn count_namespaces(syntax: &Syntax, count: &mut usize) {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == SyntaxKind::Namespace {
                *count += 1;
            }
            for child in &node.children {
                count_namespaces(child, count);
            }
        }
        _ => {}
    }
}
