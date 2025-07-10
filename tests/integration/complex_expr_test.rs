use lean_parser::Parser;
use lean_syn_expr::SyntaxKind;

#[test]
fn test_complex_expressions_individually() {
    let test_cases = vec![
        ("λ x => x + 1", "lambda expression", Some(SyntaxKind::Lambda)),
        ("∀ x : Nat, x = x", "forall expression", Some(SyntaxKind::Forall)),
        ("let x := 5; x * 2", "let expression", Some(SyntaxKind::Let)),
        ("match n with | 0 => true | _ => false", "match expression", Some(SyntaxKind::Match)),
        ("f a b c", "function application", Some(SyntaxKind::App)),
        ("1 + 2 * 3", "arithmetic expression", Some(SyntaxKind::BinOp)),
        ("{x : Nat // x > 0}", "subtype expression", None),
        ("⟨1, 2, 3⟩", "anonymous constructor", None),
        ("@id Nat", "explicit application", None),
        ("x.1", "projection", Some(SyntaxKind::Field)),
    ];

    for (input, description, expected_kind) in test_cases {
        println!("\nTesting: {} - {}", input, description);
        let mut parser = Parser::new(input);
        let result = parser.term();
        
        match result {
            Ok(syntax) => {
                println!("  ✓ Parsed successfully");
                println!("  Kind: {:?}", syntax.kind());
                if let Some(expected) = expected_kind {
                    if syntax.kind() != Some(expected) {
                        println!("  ⚠ Warning: Expected {:?}, got {:?}", expected, syntax.kind());
                    }
                }
            }
            Err(e) => {
                println!("  ✗ Failed to parse: {:?}", e);
            }
        }
    }
}

#[test]
fn test_unicode_lambda() {
    // Test different lambda syntaxes
    let test_cases = vec![
        ("λ x => x", "unicode lambda"),
        ("fun x => x", "fun keyword"),
        ("λ x : Nat => x + 1", "typed lambda"),
        ("λ x y => x + y", "multi-arg lambda"),
        ("λ (x : Nat) (y : Nat) => x + y", "multi-arg typed lambda"),
    ];
    
    for (input, description) in test_cases {
        println!("\nTesting lambda variant: {} - {}", input, description);
        let mut parser = Parser::new(input);
        let result = parser.term();
        
        match result {
            Ok(syntax) => {
                println!("  ✓ Parsed successfully as {:?}", syntax.kind());
            }
            Err(e) => {
                println!("  ✗ Failed: {:?}", e);
            }
        }
    }
}

#[test]
fn test_subtype_expression() {
    // Test subtype syntax
    let input = "{x : Nat // x > 0}";
    println!("\nTesting subtype: {}", input);
    
    let mut parser = Parser::new(input);
    let result = parser.term();
    
    match result {
        Ok(syntax) => {
            println!("  Parsed as: {:?}", syntax.kind());
            // It might be parsed as a struct literal or something else
        }
        Err(e) => {
            println!("  Failed: {:?}", e);
            println!("  This syntax needs to be implemented");
        }
    }
}

#[test]
fn test_anonymous_constructor() {
    // Test anonymous constructor syntax
    let test_cases = vec![
        ("⟨1⟩", "single element"),
        ("⟨1, 2⟩", "two elements"),
        ("⟨1, 2, 3⟩", "three elements"),
        ("⟨⟩", "empty"),
    ];
    
    for (input, description) in test_cases {
        println!("\nTesting anonymous constructor: {} - {}", input, description);
        let mut parser = Parser::new(input);
        let result = parser.term();
        
        match result {
            Ok(syntax) => {
                println!("  Parsed as: {:?}", syntax.kind());
            }
            Err(e) => {
                println!("  Failed: {:?}", e);
            }
        }
    }
}

#[test]
fn test_explicit_application() {
    // Test @ prefix for explicit application
    let test_cases = vec![
        ("@id", "bare explicit"),
        ("@id Nat", "with type arg"),
        ("@id Nat 5", "with value arg"),
        ("@List.map", "qualified name"),
    ];
    
    for (input, description) in test_cases {
        println!("\nTesting explicit application: {} - {}", input, description);
        let mut parser = Parser::new(input);
        let result = parser.term();
        
        match result {
            Ok(syntax) => {
                println!("  Parsed as: {:?}", syntax.kind());
            }
            Err(e) => {
                println!("  Failed: {:?}", e);
            }
        }
    }
}