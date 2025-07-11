-- Import common definitions
import Syntax.Prelude

namespace Syntax.Expressions.Lambda
open TestPrelude

-- Lambda expression tests

-- Basic lambda
def id := λ x => x
def const := λ x y => x

-- Unicode lambda
def id' := λ x => x
def const' := λ x y => x

-- Multiple parameters
def f1 := λ x y z => x + y + z

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
def f8 := λ (x, y) => x + y
def f9 := λ ⟨x, y⟩ => x + y

-- Nested lambdas
def curry := λ f => λ x => λ y => f (x, y)
def uncurry := λ f => λ (x, y) => f x y

-- Complex body
def f10 := λ x =>
  let y := x + 1
  let z := y * 2
  z - x

-- Lambda with local definitions
def f11 := λ x =>
  let double (n : Nat) := 2 * n
  double x + double (x + 1)

-- Pattern matching in lambda
def f12 := λ 
  | 0 => 1
  | n + 1 => 2 * n

-- Type parameters
def f13 := λ (α : Type) (x : α) => x
def f14 := λ (α : Type _) (x : α) => x
def f15 := λ (α : Type u) (x : α) => x

end Syntax.Expressions.Lambda