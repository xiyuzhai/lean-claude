-- Import common definitions
import Syntax.Prelude

namespace Syntax.Types.Basic
open TestPrelude

-- Basic type tests

-- Universe levels
universe u v w

-- Basic types
def test1 : Type := Nat
def test2 : Type := Int
def test3 : Type := String
def test4 : Type := Bool
def test5 : Type := Char
def test6 : Type := Float

-- Type universes
def test7 : Type 0 := Nat
def test8 : Type 1 := Type
def test9 : Type u := Type
def test10 : Type (u+1) := Type u
def test11 : Type (max u v) := Type u × Type v

-- Prop
def test12 : Prop := True
def test13 : Prop := False
def test14 : Prop := 1 = 1
def test15 : Prop := ∀ x : Nat, x = x

-- Sort
def test16 : Sort 0 := Prop
def test17 : Sort 1 := Type
def test18 : Sort (u+1) := Type u

-- Function types
def test19 : Type := Nat → Nat
def test20 : Type := Nat → String → Bool
def test21 : Type := (Nat → Nat) → Nat
def test22 : Type u → Type v := fun α => α → α

-- Dependent function types
def test23 : Type := (n : Nat) → Vector Nat n
def test24 : Type := {n : Nat} → Vector Nat n
def test25 : Type := ∀ {α : Type}, α → α
def test26 : Type := ∀ (α : Type) (x : α), α

-- Product types
def test27 : Type := Nat × String
def test28 : Type := Nat × String × Bool
def test29 : Type := (Nat × String) × Bool
def test30 : Type := Nat × (String × Bool)

-- Sigma types (dependent pairs)
def test31 : Type := Σ n : Nat, Vector Nat n
def test32 : Type := Σ (α : Type), α × α
def test33 : Type := Σ x : Nat, x > 0

-- Subtype
def test34 : Type := {n : Nat // n > 0}
def test35 : Type := {x : Real // x ≥ 0}

-- Option and sum types
def test36 : Type := Option Nat
def test37 : Type := Nat ⊕ String
def test38 : Type := Sum Nat String

-- List and array types
def test39 : Type := List Nat
def test40 : Type := Array String
def test41 : Type := Vector Bool 10

-- Type aliases
abbrev MyNat := Nat
abbrev Predicate α := α → Prop
abbrev BinOp α := α → α → α

def test42 : MyNat := 42
def test43 : Predicate Nat := fun n => n > 0
def test44 : BinOp Nat := fun x y => x + y

end Syntax.Types.Basic