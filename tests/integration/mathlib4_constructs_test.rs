#![allow(clippy::uninlined_format_args)]

use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
fn test_mathlib4_structures() {
    let test_cases = vec![
        // Basic structure
        (
            r#"structure Point where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq"#,
            "basic structure with deriving",
        ),
        // Structure with inheritance
        (
            r#"structure Point3D extends Point where
  z : Nat"#,
            "structure with inheritance",
        ),
        // Structure with type parameters
        (
            r#"structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β"#,
            "structure with type parameters",
        ),
        // Structure with auto params
        (
            r#"structure Group (G : Type*) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul a (mul b c) = mul (mul a b) c
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_left_inv : ∀ a, mul (inv a) a = one"#,
            "group structure",
        ),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.command();

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}", description);
                assert!(
                    contains_syntax_kind(&syntax, SyntaxKind::Structure),
                    "Should be a structure for {}",
                    description
                );
            }
            Err(e) => panic!("Failed to parse {}: {:?}", description, e),
        }
    }
}

#[test]
fn test_mathlib4_classes() {
    let test_cases = vec![
        // Basic class
        (
            r#"class Add (α : Type u) where
  add : α → α → α"#,
            "basic Add class",
        ),
        // Class with inheritance
        (
            r#"class AddGroup (G : Type u) extends Add G, Neg G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
  zero : G
  add_zero : ∀ a : G, a + zero = a
  zero_add : ∀ a : G, zero + a = a
  add_left_neg : ∀ a : G, -a + a = zero"#,
            "AddGroup class",
        ),
        // Class with outParam
        (
            r#"class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAdd : α → β → γ"#,
            "heterogeneous Add class",
        ),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.command();

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}", description);
                assert!(
                    contains_syntax_kind(&syntax, SyntaxKind::Class),
                    "Should be a class for {}",
                    description
                );
            }
            Err(e) => panic!("Failed to parse {}: {:?}", description, e),
        }
    }
}

#[test]
fn test_mathlib4_instances() {
    let test_cases = vec![
        // Basic instance
        (
            r#"instance : Add Nat where
  add := Nat.add"#,
            "basic Add instance for Nat",
        ),
        // Named instance
        (
            r#"instance natAddGroup : AddGroup Nat where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := 0
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  neg := fun _ => 0
  add_left_neg := sorry"#,
            "named AddGroup instance",
        ),
        // TODO: Instance with parameters not yet supported
        // (
        //     r#"instance [Inhabited α] : Inhabited (List α) where
        //   default := []"#,
        //     "instance with typeclass parameter",
        // ),
        // TODO: Priority instance not yet supported
        // (
        //     r#"instance (priority := low) : Coe Nat Int where
        //   coe := Int.ofNat"#,
        //     "instance with priority",
        // ),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.command();

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}", description);
                assert!(
                    contains_syntax_kind(&syntax, SyntaxKind::Instance),
                    "Should be an instance for {}",
                    description
                );
            }
            Err(e) => panic!("Failed to parse {}: {:?}", description, e),
        }
    }
}

#[test]
fn test_mathlib4_notations() {
    let test_cases = vec![
        // Infix notation
        (r#"infixl:65 " + " => HAdd.hAdd"#, "infix addition"),
        // Prefix notation
        (r#"prefix:100 "-" => Neg.neg"#, "prefix negation"),
        // TODO: Complex notation syntax not yet fully supported
        // (
        //     r#"notation:50 a " ≤ " b " ≤ " c => (a ≤ b) ∧ (b ≤ c)"#,
        //     "chained inequality notation",
        // ),
        // TODO: Scoped notation not yet fully supported
        // (
        //     r#"scoped notation:max "ℕ" => Nat"#,
        //     "scoped notation for naturals",
        // ),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.command();

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}: {:#?}", description, syntax);
                // For now, just check that it parses successfully
                // TODO: Add proper SyntaxKind checks once notation parsing is
                // complete
            }
            Err(e) => panic!("Failed to parse {}: {:?}", description, e),
        }
    }
}

#[test]
fn test_mathlib4_tactics() {
    let test_cases = vec![
        // Ring tactic
        (
            r#"example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring"#,
            "ring tactic",
        ),
        // Simp with lemmas
        (
            r#"example (xs : List α) : xs.reverse.reverse = xs := by simp [List.reverse_reverse]"#,
            "simp with lemmas",
        ),
        // Conv mode
        (
            r#"example (a b c : Nat) : a + b + c = a + c + b := by
  conv => lhs; arg 2; rw [add_comm]"#,
            "conv mode",
        ),
        // Calc mode
        (
            r#"example (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  calc a = b := h1
       _ = c := h2
       _ = d := h3"#,
            "calc proof",
        ),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.command();

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}", description);
                // Example is just a special kind of Def or Theorem
                assert!(
                    contains_syntax_kind(&syntax, SyntaxKind::Def)
                        || contains_syntax_kind(&syntax, SyntaxKind::Theorem),
                    "Should be an example (def/theorem) for {}",
                    description
                );
            }
            Err(e) => panic!("Failed to parse {}: {:?}", description, e),
        }
    }
}

#[test]
fn test_mathlib4_advanced_features() {
    let test_cases = vec![
        // TODO: Universe polymorphism syntax not yet supported
        // (
        //     r#"def id.{u} {α : Sort u} (a : α) : α := a"#,
        //     "universe polymorphic id",
        // ),
        // TODO: Match expressions in definitions not yet fully supported
        // (
        //     r#"def Vec (α : Type u) : Nat → Type u
        //   | 0 => Unit
        //   | n+1 => α × Vec α n"#,
        //     "dependent vector type",
        // ),
        // TODO: Match with multiple patterns not yet fully supported
        // (
        //     r#"def map : List α → (α → β) → List β
        //   | [], _ => []
        //   | x :: xs, f => f x :: map xs f"#,
        //     "list map with pattern matching",
        // ),
        // Simple constant
        (r#"def myNumber : Nat := 42"#, "simple constant definition"),
        // TODO: Do notation with match expressions not yet fully supported
        // (
        //     r#"def mapM [Monad m] (f : α → m β) : List α → m (List β)
        //   | [] => pure []
        //   | x :: xs => do
        //     let y ← f x
        //     let ys ← mapM f xs
        //     pure (y :: ys)"#,
        //     "monadic map",
        // ),
    ];

    for (input, description) in test_cases {
        let mut parser = Parser::new(input);
        let result = parser.command();

        match result {
            Ok(syntax) => {
                println!("Successfully parsed {}", description);
                assert!(
                    contains_syntax_kind(&syntax, SyntaxKind::Def),
                    "Should be a definition for {}",
                    description
                );
            }
            Err(e) => {
                println!("Failed to parse {}: {:?}", description, e);
                panic!("Failed to parse {}: {:?}", description, e);
            }
        }
    }
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
