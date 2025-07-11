-- Import common definitions
import Syntax.Prelude

namespace Syntax.Commands.Theorems
open TestPrelude

-- Theorem and proof command tests

-- Basic theorem
theorem trivial : 1 = 1 := rfl

-- With explicit proof term
theorem add_zero (n : Nat) : n + 0 = n := by simp

-- With parameters
theorem add_comm (x y : Nat) : x + y = y + x := by
  sorry

-- Lemma (synonym for theorem)
theorem sub_self (n : Nat) : n - n = 0 := by simp [Nat.sub_self]

-- With implicit parameters
theorem id_apply {α : Type} (x : α) : id x = x := rfl

-- With type class parameters
theorem add_comm_general {α : Type} [TestPrelude.Add α] (x y : α) : 
  TestPrelude.Add.add x y = TestPrelude.Add.add y x := by sorry

-- Proposition (same as theorem)
theorem p_implies_p (P : Prop) : P → P := fun h => h

-- Example (special kind of theorem)
example : 2 + 2 = 4 := rfl
example (x : Nat) : x + 0 = x := by simp
example {α : Type} [TestPrelude.Monoid α] (x : α) : TestPrelude.Mul.mul x TestPrelude.One.one = x := by sorry

-- With tactic proof
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => 
    rfl
  | succ n ih =>
    rw [add_succ]
    rw [ih]

-- With structured proof
theorem add_assoc (x y z : Nat) : (x + y) + z = x + (y + z) := by
  sorry

-- With have statements (simplified)
theorem exists_prime_factor (n : Nat) (h : n > 1) : 
  ∃ p, p > 1 ∧ p ∣ n := by
  have h1 : n ≥ 2 := by omega
  have h2 : n = n := by rfl
  sorry

-- With suffices (simplified)
theorem sqrt_two_irrational : Float.sqrt 2 ≠ 0 := by
  suffices Float.sqrt 2 > 0 by
    sorry
  sorry

-- With calc mode
theorem calc_example (a b c : Nat) : a + b + c = c + b + a := by
  sorry

-- With attributes
@[simp] theorem mul_zero (n : Nat) : n * 0 = 0 := by
  sorry

-- Protected theorem
protected theorem MyModule.special_theorem : True := True.intro

-- With docstring
/-- The fundamental theorem of arithmetic -/
theorem fundamental_theorem_arithmetic (n : Nat) (h : n > 1) :
  ∃ factors : List Nat, n = factors.foldl (· * ·) 1 := sorry

end Syntax.Commands.Theorems