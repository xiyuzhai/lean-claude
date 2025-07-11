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
  induction x with
  | zero => simp
  | succ x ih => simp [add_succ, ih]

-- Lemma (synonym for theorem)
lemma sub_self (n : Nat) : n - n = 0 := by simp

-- With implicit parameters
theorem id_apply {α : Type} (x : α) : id x = x := rfl

-- With type class parameters
theorem add_comm_general {α : Type} [Add α] [CommAdd α] (x y : α) : 
  x + y = y + x := CommAdd.comm x y

-- Proposition
proposition p_implies_p (P : Prop) : P → P := fun h => h

-- Example (special kind of theorem)
example : 2 + 2 = 4 := rfl
example (x : Nat) : x + 0 = x := by simp
example {α : Type} [Group α] (x : α) : x * x⁻¹ = 1 := mul_inv_eq_one

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
  induction z with
  | zero =>
    simp
  | succ z ih =>
    rw [add_succ, add_succ, add_succ]
    rw [ih]

-- With have statements
theorem exists_prime_factor (n : Nat) (h : n > 1) : 
  ∃ p, Prime p ∧ p ∣ n := by
  have h1 : n ≥ 2 := by linarith
  have h2 : ∃ factors, n = factors.prod := factorization_exists n
  sorry

-- With suffices
theorem sqrt_two_irrational : Irrational (sqrt 2) := by
  suffices ∀ p q : Nat, q ≠ 0 → p * p ≠ 2 * q * q by
    sorry
  intro p q hq contra
  sorry

-- With calc mode
theorem calc_example (a b c : Nat) : a + b + c = c + b + a := by
  calc a + b + c 
    = (a + b) + c   := by rfl
    = c + (a + b)   := by rw [add_comm]
    = c + (b + a)   := by rw [add_comm a b]
    = c + b + a     := by rfl

-- With attributes
@[simp] theorem mul_zero (n : Nat) : n * 0 = 0 := by
  induction n <;> simp [*, mul_succ]

-- Protected theorem
protected theorem MyModule.special_theorem : True := trivial

-- With docstring
/-- The fundamental theorem of arithmetic -/
theorem fundamental_theorem_arithmetic (n : Nat) (h : n > 1) :
  ∃! factors : List Prime, n = factors.prod := sorry

end Syntax.Commands.Theorems