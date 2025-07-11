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

-- Common lemmas for examples (not real proofs)
theorem add_succ (n m : Nat) : n + (m + 1) = (n + m) + 1 := by sorry
theorem mul_succ (n m : Nat) : n * (m + 1) = n * m + n := by sorry

-- CommAdd class for examples
class CommAdd (α : Type) extends Add α where
  add_comm : ∀ x y : α, add x y = add y x

end TestPrelude

open TestPrelude