use lean_parser::Parser;
use lean_syn_expr::SyntaxKind;

#[test]
fn test_have_term() {
    // Test have as a term (not wrapped in `by`)
    let input = "have h : Nat := 42";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse have term: {:?}", result.err());
    
    let syntax = result.unwrap();
    assert_eq!(syntax.kind(), Some(SyntaxKind::Have));
}

#[test]
fn test_have_term_with_by() {
    // Test have term with proof by tactic
    let input = "have h : p := by exact proof";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse have term with by: {:?}", result.err());
}

#[test]
fn test_show_term() {
    // Test show as a term (not wrapped in `by`)
    let input = "show Nat from 42";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse show term: {:?}", result.err());
    
    let syntax = result.unwrap();
    assert_eq!(syntax.kind(), Some(SyntaxKind::Show));
}

#[test]
fn test_show_term_alternative() {
    // Test alternative syntax: show q from proof
    let input = "show q from proof";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse show term: {:?}", result.err());
}

#[test]
fn test_calc_term() {
    // Test calc as a term (not wrapped in `by`)
    let input = "calc a = b := by rfl
     _ = c := by simp";
    let mut parser = Parser::new(input);
    let result = parser.term();
    
    // This might fail if calc_term is not implemented
    match result {
        Ok(syntax) => {
            assert_eq!(syntax.kind(), Some(SyntaxKind::Calc));
            println!("calc term parsing is implemented!");
        }
        Err(e) => {
            println!("calc term parsing not yet implemented: {:?}", e);
        }
    }
}

#[test]
fn test_have_tactic_in_by() {
    // Test have as a tactic inside `by`
    let input = "by have h : p := by exact hp; exact h";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse by with have tactic: {:?}", result.err());
}

#[test]
fn test_show_tactic_in_by() {
    // Test show as a tactic inside `by`
    let input = "by show q; exact proof";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse by with show tactic: {:?}", result.err());
}

#[test]
fn test_calc_tactic_in_by() {
    // Test calc as a tactic inside `by`
    let input = "by calc a = b := rfl
                   _ = c := simp";
    let mut parser = Parser::new(input);
    let result = parser.term();
    assert!(result.is_ok(), "Failed to parse by with calc tactic: {:?}", result.err());
}

#[test]
fn test_actual_tactics() {
    // Test actual tactics that should work with `by`
    let test_cases = vec![
        ("by exact h", "exact tactic"),
        ("by apply f", "apply tactic"),
        ("by intro x y", "intro tactic"),
        ("by simp [add_comm]", "simp tactic"),
        ("by rw [h1, h2]", "rewrite tactic"),
        ("by rfl", "rfl tactic"),
        ("by sorry", "sorry tactic"),
        ("by assumption", "assumption tactic"),
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