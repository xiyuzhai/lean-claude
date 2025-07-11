-- Notation examples for Lean 4

-- Simple notation
notation "⟨" a ", " b "⟩" => Prod.mk a b

-- Infix notation with precedence
infix:50 " ⊕ " => fun x y => x + y

-- Prefix notation
prefix:75 "√" => Nat.sqrt

-- Postfix notation
postfix:80 "!" => factorial

-- Left associative infix
infixl:65 " ⊗ " => HMul.hMul

-- Right associative infix
infixr:60 " ⊞ " => fun x y => x + y * 2

-- Complex notation with multiple parts
notation "if" p "then" a "else" b => ite p a b

-- Notation with precedence specification
notation:max "⌊" a "⌋" => Int.floor a

-- Mixfix notation
notation a " choose " b => Nat.choose a b

-- Mathematical notation
notation "∑" => List.sum
notation "∏" => List.prod

-- Set notation
notation "∅" => Set.empty
notation a " ∈ " s => Set.mem a s
notation a " ∉ " s => ¬Set.mem a s

-- Function composition
infixr:90 " ∘ " => Function.comp

-- Logical operators
notation "¬" => Not
infixr:35 " ∧ " => And
infixr:30 " ∨ " => Or
infixr:25 " → " => implies
infixl:20 " ↔ " => Iff

-- Comparison operators  
infix:50 " ≤ " => LE.le
infix:50 " ≥ " => GE.ge
infix:50 " ≠ " => Ne

-- List operations
infixr:67 " :: " => List.cons
infixl:65 " ++ " => List.append

-- Type operations
infixr:35 " × " => Prod
notation "ℕ" => Nat
notation "ℤ" => Int
notation "ℝ" => Real

-- Bracket notation
notation "[" l "]" => List.mk l
notation "{" s "}" => Set.mk s

-- Quantifiers
notation "∀" => forall
notation "∃" => exists

-- Lambda notation (alternative)
notation "λ" => fun

-- Equality and membership
infix:50 " = " => Eq
infix:50 " ≈ " => Equiv

-- Arrow types
infixr:25 " ⟶ " => Function.type
notation a " ⟹ " b => a → b

-- Custom mathematical operators
infixl:70 " ⊙ " => customOp1
infixr:65 " ⊛ " => customOp2
prefix:80 "△" => customUnary

-- Notation for common patterns
notation "match" e "with" arms => match e with arms
notation "let" x " := " v " in " b => let x := v; b