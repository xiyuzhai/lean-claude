-- Import common definitions
import Syntax.Prelude

namespace Syntax.Types.Forall
open TestPrelude

-- Forall (Pi) type tests

-- Basic forall
def test1 : Prop := ∀ x : Nat, x = x
def test2 : Prop := ∀ x y : Nat, x + y = y + x
def test3 : Prop := ∀ (x y z : Nat), x + (y + z) = (x + y) + z

-- Unicode syntax
def test4 : Prop := ∀ x : Nat, x = x
def test5 : Type := Π x : Nat, Vector Nat x

-- Implicit parameters
def test6 : Type := ∀ {α : Type}, α → α
def test7 : Type := ∀ {α : Type} {β : Type}, (α → β) → α → β

-- Mixed parameters
def test8 : Type := ∀ {α : Type} (x : α) {β : Type} (y : β), α × β

-- Instance implicit
def test9 : Type := ∀ [Monad m], m α → (α → m β) → m β

-- Strict implicit
def test10 : Type := ∀ ⦃α : Type⦄, α → α

-- With type classes
def test11 : Prop := ∀ α [Add α] (x y : α), x + y = y + x
def test12 : Type := ∀ {m : Type → Type} [Monad m], m Nat

-- Dependent types
def test13 : Type := ∀ (n : Nat), Vector Nat n → Nat
def test14 : Type := ∀ (α : Type) (x : α), x = x

-- Nested forall
def test15 : Prop := ∀ x, (∀ y, P x y) → Q x
def test16 : Type := ∀ α, (∀ β, α → β → β) → α → α

-- With predicates
def test17 : Prop := ∀ x, x > 0 → x ≥ 1
def test18 : Prop := ∀ x y, x < y → ∃ z, x < z ∧ z < y

-- Forall with patterns
def test19 : Prop := ∀ (x, y), x + y = y + x
def test20 : Prop := ∀ ⟨x, y, z⟩, x + y + z = z + y + x

-- Bounded quantification
def test21 : Prop := ∀ x ∈ s, P x
def test22 : Prop := ∀ x ∈ s, ∀ y ∈ t, R x y

-- Type family
def test23 : (n : Nat) → Type := fun n => Vector Nat n
def test24 : Type 1 := ∀ α : Type, Type

-- Higher-order
def test25 : Type := ∀ (P : Nat → Prop), (∀ n, P n) → P 0
def test26 : Type := ∀ (f : ∀ α, α → α), f Nat 0 = 0

-- With naming patterns
def test27 : Prop := ∀ x y : Nat, ∀ h : x < y, ∃ z, x < z ∧ z < y

end Syntax.Types.Forall