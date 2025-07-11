-- Common type definitions used across test files

namespace TestPrelude

-- Type variables
variable {α : Type} {β : Type} {γ : Type} {δ : Type}

-- Common type classes
class Zero (α : Type) where
  zero : α

class One (α : Type) where
  one : α

class Add (α : Type) where
  add : α → α → α

class Mul (α : Type) where
  mul : α → α → α

class Monoid (α : Type) extends One α, Mul α where
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)

-- Basic instances
instance : Zero Nat where
  zero := 0

instance : One Nat where
  one := 1

instance : Add Nat where
  add := Nat.add

instance : Mul Nat where
  mul := Nat.mul

-- Helper functions
def sqrt : Float → Float := Float.sqrt

-- Common predicates
def P : Prop := True
def Q : Prop := False
def R : Prop := True

-- Vector type (simplified)
inductive Vector (α : Type) : Nat → Type where
  | nil : Vector α 0
  | cons : ∀ {n : Nat}, α → Vector α n → Vector α (n + 1)

-- Named type for examples
structure Named where
  name : String

-- Color type for examples
inductive Color where
  | red
  | green
  | blue

-- Point structure for examples
structure Point where
  x : Float
  y : Float
  z : Float

-- Function type abbreviation
abbrev F := Nat → Nat

-- Common functions for examples
def const (x : α) (_ : β) : α := x
def add (x y : Nat) : Nat := x + y
def mul (x y : Nat) : Nat := x * y
def f (x : Nat) : Nat := x + 1
def g (x : Nat) : Nat := x * 2
def h (x : Nat) : Nat := x - 1
def map (f : α → β) (xs : List α) : List β := List.map f xs
def fold (f : α → β → α) (init : α) (xs : List β) : α := List.foldl f init xs
def filter (p : α → Bool) (xs : List α) : List α := List.filter p xs

-- Example list for testing
def list : List Nat := [1, 2, 3, 4, 5]

-- Point construction function
def mkPoint (x y : Float) : Point := ⟨x, y, 0⟩

-- Example point for testing
def point : Point := ⟨1.0, 2.0, 3.0⟩

-- Processing functions for pipeline examples
def computeValue (x : Nat) : Nat := x * 2
def process (x : Nat) : Nat := x + 1
def postProcess (x : Nat) : Nat := x * 3
def finalize (x : Nat) : Nat := x

-- Variables for examples
variable (x y z : Nat)
variable (p : Nat → Bool)

-- Common lemmas for examples (not real proofs)
theorem add_succ (n m : Nat) : n + (m + 1) = (n + m) + 1 := by sorry
theorem mul_succ (n m : Nat) : n * (m + 1) = n * m + n := by sorry

-- CommAdd class for examples
class CommAdd (α : Type) extends Add α where
  add_comm : ∀ x y : α, add x y = add y x

end TestPrelude

open TestPrelude