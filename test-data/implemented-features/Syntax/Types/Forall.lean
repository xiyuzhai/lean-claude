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
def test5 : Type := ∀ x : Nat, Vector Nat x

-- Implicit parameters
def test6 : Type 1 := ∀ {α : Type}, α → α
def test7 : Type 1 := ∀ {α : Type} {β : Type}, (α → β) → α → β

-- Mixed parameters
def test8 : Type 1 := ∀ {α : Type} (x : α) {β : Type} (y : β), α × β

-- Instance implicit (simplified)
def test9 : Type 1 := ∀ (m : Type → Type), m Nat → (Nat → m Bool) → m Bool

-- Strict implicit
def test10 : Type 1 := ∀ {α : Type}, α → α

-- With type classes
def test11 : Prop := ∀ α [TestPrelude.Add α] (x y : α), TestPrelude.Add.add x y = TestPrelude.Add.add y x
def test12 : Type 1 := ∀ {m : Type → Type}, m Nat

-- Dependent types
def test13 : Type := ∀ (n : Nat), Vector Nat n → Nat
def test14 : Prop := ∀ (α : Type) (x : α), x = x

-- Nested forall
variable (P : Nat → Nat → Prop) (Q : Nat → Prop)
def test15 : Prop := ∀ x, (∀ y, P x y) → Q x
def test16 : Type 1 := ∀ α : Type, (Nat → α → α) → α → α

-- With predicates
def test17 : Prop := ∀ x, x > 0 → x ≥ 1
def test18 : Prop := ∀ x y : Nat, x < y → ∃ z : Nat, x < z ∧ z < y

-- Forall with patterns
def test19 : Prop := ∀ p : Nat × Nat, p.1 + p.2 = p.2 + p.1
def test20 : Prop := ∀ p : Nat × Nat × Nat, p.1 + p.2.1 + p.2.2 = p.2.2 + p.2.1 + p.1

-- Bounded quantification (simplified)
variable (s t : List Nat) (R : Nat → Nat → Prop)
def test21 : Prop := ∀ x ∈ s, P x 0
def test22 : Prop := ∀ x ∈ s, ∀ y ∈ t, R x y

-- Type family
def test23 : (n : Nat) → Type := fun n => Vector Nat n
def test24 : Type 1 := ∀ _α : Type, Type

-- Higher-order
def test25 : Prop := ∀ (P : Nat → Prop), (∀ n, P n) → P 0
def test26 : Prop := ∀ (f : ∀ α, α → α), f Nat 0 = 0

-- With naming patterns
def test27 : Prop := ∀ x y : Nat, ∀ _h : x < y, ∃ z, x < z ∧ z < y

end Syntax.Types.Forall