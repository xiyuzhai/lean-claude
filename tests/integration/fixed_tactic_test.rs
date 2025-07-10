use lean_parser::Parser;
use lean_syn_expr::SyntaxKind;

#[test]
fn test_have_as_term() {
    // These are TERM expressions, not tactics
    let input = "have h : p := by exact proof";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse have term: {:?}", result.err());
    
    let syntax = result.unwrap();
    assert_eq!(syntax.kind(), Some(SyntaxKind::Have));
}

#[test]
fn test_show_as_term() {
    // This is a TERM expression, not a tactic
    let input = "show q from proof";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse show term: {:?}", result.err());
    
    let syntax = result.unwrap();
    assert_eq!(syntax.kind(), Some(SyntaxKind::Show));
}

#[test]
fn test_calc_as_term() {
    // This is a TERM expression, not a tactic
    let input = "calc a = b := by rfl
     _ = c := by simp";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse calc term: {:?}", result.err());
    
    let syntax = result.unwrap();
    assert_eq!(syntax.kind(), Some(SyntaxKind::Calc));
}

#[test]
fn test_tactics_that_should_actually_work() {
    // These are the actual tactics that should work with `by`
    let test_cases = vec![
        ("by exact h", "exact tactic"),
        ("by apply f", "apply tactic"),
        ("by intros x y", "intros tactic"),  // intro takes one arg, intros takes multiple
        ("by simp [add_comm, mul_comm]", "simp tactic"),
        ("by rw [h1, h2]", "rewrite tactic"),
        ("by rfl", "rfl tactic"),
        ("by sorry", "sorry tactic"),
        ("by assumption", "assumption tactic"),
        ("by constructor", "constructor tactic"),
        // Tactic sequences
        ("by exact h; simp", "tactic sequence"),
        ("by intro x; apply f", "intro then apply"),
        // Tactic alternatives
        ("by exact h1 <|> exact h2", "tactic alternative"),
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
        
        let syntax = result.unwrap();
        if syntax.kind() != Some(SyntaxKind::By) {
            println!("Unexpected syntax kind for '{}': {:?}", input, syntax.kind());
        }
        assert_eq!(syntax.kind(), Some(SyntaxKind::By));
    }
}

#[test]
fn test_cases_with_patterns() {
    // The cases in the original test was correct
    let input = "by cases h with | inl h => sorry | inr h => sorry";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse cases with patterns: {:?}", result.err());
}

#[test]
fn test_induction_tactic() {
    // Simple induction
    let input = "by induction n";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse induction: {:?}", result.err());
}

#[test]
fn test_have_as_tactic_in_sequence() {
    // `have` can be used as a tactic inside a tactic sequence
    let input = "by have h : p := by exact hp; exact h";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse have tactic in sequence: {:?}", result.err());
}

#[test]
fn test_show_as_tactic_in_sequence() {
    // `show` can be used as a tactic
    let input = "by show q; exact proof";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse show tactic in sequence: {:?}", result.err());
}

#[test]
fn test_calc_as_tactic() {
    // `calc` can be used as a tactic (this is different from calc term!)
    let input = "by calc a = b := rfl
              _ = c := simp";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse calc tactic: {:?}", result.err());
}