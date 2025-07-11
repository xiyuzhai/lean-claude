-- Import common definitions
import Syntax.Prelude

namespace Syntax.Expressions.Lambda
open TestPrelude

-- Lambda expression tests

-- Basic lambda
def id : Nat → Nat := λ x => x
def const : Nat → Nat → Nat := λ x _y => x

-- Unicode lambda
def id' : Nat → Nat := λ x => x
def const' : Nat → Nat → Nat := λ x _y => x

-- Multiple parameters
def f1 : Nat → Nat → Nat → Nat := λ x y z => x + y + z

-- With type annotations
def f2 := λ (x : Nat) => x + 1
def f3 := λ (x : Nat) (y : Nat) => x + y
def f4 := λ (x y : Nat) => x + y  -- Shared type annotation

-- Implicit parameters
def f5 := λ {α : Type} (x : α) => x
def f6 := λ {α : Type} {β : Type} (f : α → β) (x : α) => f x

-- Mixed parameter types
def f7 := λ {α : Type} (x : α) {β : Type} (y : β) => (x, y)

-- With pattern matching
def f8 : Nat × Nat → Nat := λ (x, y) => x + y
def f9 : Point → Float := λ ⟨x, y, z⟩ => x + y + z

-- Nested lambdas
def curry : (Nat × Nat → Nat) → Nat → Nat → Nat := λ f => λ x => λ y => f (x, y)
def uncurry : (Nat → Nat → Nat) → (Nat × Nat → Nat) := λ f => λ (x, y) => f x y

-- Complex body
def f10 : Nat → Nat := λ x =>
  let y := x + 1
  let z := y * 2
  z - x

-- Lambda with local definitions
def f11 : Nat → Nat := λ x =>
  let double (n : Nat) := 2 * n
  double x + double (x + 1)

-- Pattern matching in lambda
def f12 : Nat → Nat := λ 
  | 0 => 1
  | n + 1 => 2 * n

-- Type parameters
def f13 : (α : Type) → α → α := λ (α : Type) (x : α) => x
def f14 : (α : Type) → α → α := λ (α : Type) (x : α) => x
def f15 : (α : Type) → α → α := λ (α : Type) (x : α) => x

end Syntax.Expressions.Lambda