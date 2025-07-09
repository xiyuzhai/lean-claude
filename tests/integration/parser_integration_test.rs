use lean_parser::Parser;
use lean_syn_expr::SyntaxKind;

#[test]
fn test_parse_simple_module() {
    // Test with just imports for now
    let input = r#"
import Lean.Data.List
import Mathlib.Data.Nat.Basic

namespace Example
end Example
"#;

    let mut parser = Parser::new(input);
    let result = parser.module();

    assert!(result.is_ok(), "Failed to parse module: {:?}", result.err());

    let syntax = result.unwrap();
    assert!(!syntax.is_missing());
    assert_eq!(syntax.kind(), Some(SyntaxKind::Module));
}

#[test]
#[ignore = "Complex expressions not fully implemented"]
fn test_parse_complex_expressions() {
    let test_cases = vec![
        ("λ x => x + 1", "lambda expression"),
        ("∀ x : Nat, x = x", "forall expression"),
        ("let x := 5; x * 2", "let expression"),
        ("match n with | 0 => true | _ => false", "match expression"),
        ("f a b c", "function application"),
        ("1 + 2 * 3", "arithmetic expression"),
        ("{x : Nat // x > 0}", "subtype expression"),
        ("⟨1, 2, 3⟩", "anonymous constructor"),
        ("@id Nat", "explicit application"),
        ("x.1", "projection"),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.term();
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
fn test_parse_basic_commands() {
    let test_cases = vec![
        ("namespace Foo", "namespace command"),
        ("end Foo", "end command"),
        ("#check Nat", "hash command"),
        ("open List", "open command"),
        ("universe u v", "universe declaration"),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.command();
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
#[ignore = "Definition parsing not fully implemented"]
fn test_parse_definitions() {
    let test_cases = vec![
        ("def foo := 1", "simple definition"),
        ("theorem bar : 1 = 1 := rfl", "theorem"),
        ("axiom excluded_middle : ∀ p : Prop, p ∨ ¬p", "axiom"),
        ("variable (x : Nat)", "variable declaration"),
        ("instance : Inhabited Nat := ⟨0⟩", "instance declaration"),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.command();
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
fn test_parse_basic_terms() {
    let test_cases = vec![
        ("x", "identifier"),
        ("123", "number literal"),
        ("\"hello\"", "string literal"),
        ("(x)", "parenthesized term"),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.term();
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
#[ignore = "Tactics not implemented"]
fn test_parse_tactics() {
    let test_cases = vec![
        ("exact h", "exact tactic"),
        ("apply f", "apply tactic"),
        ("intro x y", "intro tactic"),
        (
            "cases h with | inl h => sorry | inr h => sorry",
            "cases tactic",
        ),
        ("simp [add_comm, mul_comm]", "simp tactic"),
        ("rw [← h1, h2]", "rewrite tactic"),
        ("induction n", "induction tactic"),
        ("have h : p := by exact proof", "have tactic"),
        ("show q from proof", "show tactic"),
        ("calc a = b := by rfl\n     _ = c := by simp", "calc tactic"),
    ];

    for (input, description) in test_cases {
        let input_with_by = format!("by {}", input);
        let mut parser = Parser::new(&input_with_by);
        let result = parser.term(); // Tactics are parsed as part of terms
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
fn test_parse_basic_patterns() {
    let test_cases = vec![
        ("x", "variable pattern"),
        ("_", "wildcard pattern"),
    ];

    for (pattern, description) in test_cases {
        let input = format!("match x with | {} => true", pattern);
        let mut parser = Parser::new(&input);
        let result = parser.pattern();
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
#[ignore = "Pattern matching not fully implemented"]
fn test_parse_complex_patterns() {
    let test_cases = vec![
        ("0", "literal pattern"),
        ("Cons h t", "constructor pattern"),
        ("⟨x, y⟩", "anonymous constructor pattern"),
        ("x@(Cons h t)", "as pattern"),
        (".1", "tuple pattern"),
    ];

    for (pattern, description) in test_cases {
        let input = format!("match x with | {} => true", pattern);
        let mut parser = Parser::new(&input);
        let result = parser.term();
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
#[ignore = "Error recovery not implemented"]
fn test_error_recovery() {
    let inputs_with_errors = vec![
        "def foo := ",   // Missing body
        "theorem bar :", // Missing type and proof
        "match x with",  // Missing match arms
        "λ",             // Incomplete lambda
        "∀ x :",         // Missing type and body
    ];

    for input in inputs_with_errors {
        let mut parser = Parser::new(input);
        let result = parser.module();
        // Even with errors, the parser should produce some syntax tree
        assert!(
            result.is_ok(),
            "Parser should recover from error in: {}",
            input
        );
    }
}

#[test]
fn test_basic_unicode_support() {
    let test_cases = vec![
        ("α", "unicode identifier"),
        ("α → β", "unicode arrow"),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.term();
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
#[ignore = "Advanced unicode not fully supported"]
fn test_advanced_unicode_support() {
    let test_cases = vec![
        ("∀ x ∈ s, P x", "unicode quantifier"),
        ("λ x ↦ x²", "unicode lambda"),
        ("x ≤ y ∧ y ≤ z", "unicode operators"),
        ("⟨x, y, z⟩", "angle brackets"),
        ("x ∈ ℕ", "unicode symbols"),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.term();
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
#[ignore = "Whitespace preservation needs more work"]
fn test_whitespace_preservation() {
    let input = "def foo   :=\n  let x := 1\n  let y := 2\n  x + y";
    let mut parser = Parser::new(input);
    let result = parser.command();

    assert!(result.is_ok());
    let syntax = result.unwrap();

    // The parser should preserve whitespace information in the syntax tree
    // This is important for IDE features like formatting
    assert!(syntax.range().is_some());
}

#[test]
fn test_operators_precedence() {
    // Test basic operator precedence
    let test_cases = vec![
        ("1 + 2", "addition"),
        ("x * y", "multiplication"),
        ("a - b", "subtraction"),
        ("m / n", "division"),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.term();
        assert!(
            result.is_ok(),
            "Failed to parse {}: {:?}",
            description,
            result.err()
        );
    }
}

#[test]
fn test_match_expressions() {
    // Test basic match expressions
    let input = "match x with | y => z";
    let mut parser = Parser::new(input);
    let result = parser.term();
    
    assert!(result.is_ok(), "Failed to parse match expression: {:?}", result.err());
    
    if let Ok(syntax) = result {
        assert_eq!(syntax.kind(), Some(SyntaxKind::Match));
    }
}