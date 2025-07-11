-- Import common definitions
import Syntax.Prelude

namespace Syntax.Unicode.Symbols
open TestPrelude

-- Unicode symbol tests

-- Greek letters
def α : Type := Nat
def β : Type := String
def γ : Type := Bool
def Δ : Nat → Nat := fun n => n + 1
def ε : Float := 0.0001
def λ := fun x => x
def μ : Nat := 42
def π : Float := 3.14159
def σ : Type → Type := Option
def τ : Type := Unit
def φ : Nat → Nat → Nat := fun x y => x + y
def ψ : Prop := True
def ω : Nat := 0

-- Mathematical symbols
def test1 : Prop := ∀ x : Nat, x = x
def test2 : Prop := ∃ x : Nat, x > 0
def test3 : Type := Nat → Nat
def test4 : Prop := P ∧ Q
def test5 : Prop := P ∨ Q
def test6 : Prop := ¬P
def test7 : Prop := P → Q
def test8 : Prop := P ↔ Q
def test9 : Prop := x ∈ s
def test10 : Prop := x ∉ s
def test11 : Type := α × β
def test12 : Type := α ⊕ β
def test13 : Type := Σ x : α, P x
def test14 : Type := Π x : α, P x

-- Relations
def test15 : Prop := x ≤ y
def test16 : Prop := x ≥ y
def test17 : Prop := x ≠ y
def test18 : Prop := x ≈ y
def test19 : Prop := x ≡ y
def test20 : Prop := x ∼ y
def test21 : Prop := x ≃ y
def test22 : Prop := x ≅ y

-- Set operations
def test23 := s ∪ t
def test24 := s ∩ t
def test25 := s ⊆ t
def test26 := s ⊂ t
def test27 := s ⊇ t
def test28 := s ⊃ t
def test29 := ∅ -- empty set

-- Arrows and functions
def test30 : Type := α → β
def test31 : Type := α ↦ β
def test32 := f ∘ g
def test33 : Type := α ⇒ β
def test34 : α := x ↦ f x

-- Brackets and delimiters
def test35 := ⟨x, y, z⟩
def test36 := ⟦x⟧
def test37 := ⌊x⌋  -- floor
def test38 := ⌈x⌉  -- ceiling
def test39 := {x // P x}

-- Superscript and subscript
def test40 := x⁻¹
def test41 := x²
def test42 := x³
def test43 := xⁿ
def test44 := x₀
def test45 := x₁
def test46 := x₂

-- Other mathematical notation
def test47 := x ⊗ y  -- tensor product
def test48 := x ⊕ y  -- direct sum
def test49 := x ⊙ y  -- odot
def test50 := x • y  -- scalar multiplication
def test51 := ∞     -- infinity
def test52 := ∂ f   -- partial derivative
def test53 := ∇ f   -- gradient
def test54 := ∑ i in s, f i  -- sum
def test55 := ∏ i in s, f i  -- product
def test56 := ∫ x in a..b, f x  -- integral

-- Logic symbols
def test57 : Prop := ⊤  -- true
def test58 : Prop := ⊥  -- false
def test59 : Prop := P ⊢ Q  -- entails
def test60 : Prop := P ⊣ Q

end Syntax.Unicode.Symbols