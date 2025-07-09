use lean_parser::parser::Parser;

fn parse_tactic(input: &str) -> Result<lean_syn_expr::Syntax, lean_parser::error::ParseError> {
    let mut parser = Parser::new(input);
    parser.by_tactic()
}

fn parse_module(input: &str) -> Result<lean_syn_expr::Syntax, lean_parser::error::ParseError> {
    let mut parser = Parser::new(input);
    parser.module()
}

#[test]
fn test_basic_tactics() {
    let test_cases = vec![
        "by exact h",
        "by apply f",
        "by intro x",
        "by intros x y z",
        "by rfl",
        "by sorry",
        "by assumption",
        "by contradiction",
    ];

    for input in test_cases {
        let result = parse_tactic(input);
        match &result {
            Ok(_) => {}
            Err(e) => eprintln!("Parse error for '{input}': {e:?}"),
        }
        assert!(result.is_ok(), "Failed to parse: {input}");
    }
}

#[test]
fn test_tactic_sequences() {
    let test_cases = vec![
        "by intro x; exact x",
        "by intro x; intro y; exact f x y",
        "by simp; rfl",
        "by try simp; exact h",
    ];

    for input in test_cases {
        let result = parse_tactic(input);
        match &result {
            Ok(_) => {}
            Err(e) => eprintln!("Parse error for '{input}': {e:?}"),
        }
        assert!(result.is_ok(), "Failed to parse: {input}");
    }
}

#[test]
fn test_tactic_alternatives() {
    let test_cases = vec![
        "by exact h <|> sorry",
        "by simp <|> rfl <|> sorry",
        "by intro x; exact x <|> assumption",
    ];

    for input in test_cases {
        let result = parse_tactic(input);
        match &result {
            Ok(_) => {}
            Err(e) => eprintln!("Parse error for '{input}': {e:?}"),
        }
        assert!(result.is_ok(), "Failed to parse: {input}");
    }
}

#[test]
fn test_tactic_combinators() {
    let test_cases = vec![
        "by repeat intro",
        "by try simp",
        "by all_goals simp",
        "by focus exact h",
        "by first | exact h1 | exact h2 | sorry",
    ];

    for input in test_cases {
        let result = parse_tactic(input);
        match &result {
            Ok(_) => {}
            Err(e) => eprintln!("Parse error for '{input}': {e:?}"),
        }
        assert!(result.is_ok(), "Failed to parse: {input}");
    }
}

#[test]
fn test_simp_tactic() {
    let test_cases = vec![
        "by simp",
        "by simp [h1, h2]",
        "by simp [-neg_neg, add_comm]",
        "by simp [h1, -h2, h3]",
    ];

    for input in test_cases {
        let result = parse_tactic(input);
        match &result {
            Ok(_) => {}
            Err(e) => eprintln!("Parse error for '{input}': {e:?}"),
        }
        assert!(result.is_ok(), "Failed to parse: {input}");
    }
}

#[test]
fn test_rewrite_tactic() {
    let test_cases = vec![
        "by rw [h]",
        "by rewrite [h1, h2]",
        "by rw [←h]",
        "by rw [<-h]",
        "by rw [h1, ←h2, h3]",
    ];

    for input in test_cases {
        let result = parse_tactic(input);
        match &result {
            Ok(_) => {}
            Err(e) => eprintln!("Parse error for '{input}': {e:?}"),
        }
        assert!(result.is_ok(), "Failed to parse: {input}");
    }
}

#[test]
fn test_cases_induction_tactics() {
    let test_cases = vec![
        "by cases h",
        "by cases h with | inl a => sorry | inr b => sorry",
        "by induction n",
        "by induction n with | zero => sorry | succ n ih => sorry",
        "by induction xs generalizing ys",
    ];

    for input in test_cases {
        let result = parse_tactic(input);
        match &result {
            Ok(_) => {}
            Err(e) => eprintln!("Parse error for '{input}': {e:?}"),
        }
        assert!(result.is_ok(), "Failed to parse: {input}");
    }
}

#[test]
fn test_have_let_show_tactics() {
    let test_cases = vec![
        "by have h : P := proof",
        "by have : P := by exact proof",
        "by let x := 42",
        "by show P",
    ];

    for input in test_cases {
        let result = parse_tactic(input);
        match &result {
            Ok(_) => {}
            Err(e) => eprintln!("Parse error for '{input}': {e:?}"),
        }
        assert!(result.is_ok(), "Failed to parse: {input}");
    }
}

#[test]
fn test_calc_tactic() {
    let test_cases = vec![
        r#"by calc x = y := by rfl
                _ = z := by simp"#,
        r#"by calc x < y := h1
                _ ≤ z := h2"#,
    ];

    for input in test_cases {
        let result = parse_tactic(input);
        match &result {
            Ok(_) => {},
            Err(e) => eprintln!("Parse error for calc: {e:?}"),
        }
        assert!(result.is_ok(), "Failed to parse calc: {input}");
    }
}

#[test]
fn test_tactics_in_proofs() {
    let test_cases = vec![
        "theorem foo : P := by exact h",
        "theorem bar (x : Nat) : x = x := by rfl",
        "def baz : Nat := by exact 42",
        r#"theorem complex : ∀ x, P x := by
            intro x
            cases x with
            | zero => sorry
            | succ n => exact h n"#,
    ];

    for input in test_cases {
        let result = parse_module(input);
        assert!(
            result.is_ok(),
            "Failed to parse proof with tactics: {input}"
        );
    }
}
