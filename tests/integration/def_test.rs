use lean_parser::Parser;
use lean_syn_expr::SyntaxKind;

#[test]
fn test_definitions() {
    let test_cases = vec![
        ("def foo := 1", "simple definition", true),
        ("def foo : Nat := 1", "typed definition", true),
        ("def foo (x : Nat) := x + 1", "function definition", true),
        ("def foo (x y : Nat) : Nat := x + y", "multi-param function", true),
        ("theorem bar : 1 = 1 := rfl", "theorem", true),
        ("theorem bar (x : Nat) : x = x := rfl", "theorem with params", true),
        ("axiom excluded_middle : ∀ p : Prop, p ∨ ¬p", "axiom", true),
        ("variable (x : Nat)", "variable declaration", true),
        ("variable (x y : Nat) (z : Int)", "multiple variables", true),
        ("instance : Inhabited Nat := ⟨0⟩", "instance declaration", true),
        ("constant c : Nat", "constant declaration", true),
    ];
    
    for (input, description, should_succeed) in test_cases {
        println!("\nTesting: {} - {}", input, description);
        let mut parser = Parser::new(input);
        let result = parser.command();
        
        match (result, should_succeed) {
            (Ok(syntax), true) => {
                println!("  ✓ Parsed successfully as {:?}", syntax.kind());
                match syntax.kind() {
                    Some(SyntaxKind::Def) => println!("    Definition command"),
                    Some(SyntaxKind::Theorem) => println!("    Theorem command"),
                    Some(SyntaxKind::Axiom) => println!("    Axiom command"),
                    Some(SyntaxKind::Variable) => println!("    Variable command"),
                    Some(SyntaxKind::Instance) => println!("    Instance command"),
                    Some(SyntaxKind::Constant) => println!("    Constant command"),
                    _ => println!("    Unexpected kind: {:?}", syntax.kind()),
                }
            }
            (Ok(_), false) => {
                println!("  ! Parsed but expected failure");
            }
            (Err(e), true) => {
                println!("  ✗ Failed but expected success: {:?}", e);
            }
            (Err(e), false) => {
                println!("  ✓ Failed as expected: {:?}", e);
            }
        }
    }
}