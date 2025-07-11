-- Import common definitions
import Syntax.Prelude

namespace Syntax.Tactics.Basic
open TestPrelude

-- Basic tactic tests

theorem test1 : True := by
  trivial

theorem test2 : 1 = 1 := by
  rfl

theorem test3 (P : Prop) (h : P) : P := by
  exact h

theorem test4 (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp

theorem test5 (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h; exact hp  -- semicolon for sequencing

theorem test6 (P Q : Prop) (h : P ∧ Q) : P := by
  cases h with
  | mk hp hq => exact hp

theorem test7 (n : Nat) : n = n := by
  cases n
  · rfl  -- case zero
  · rfl  -- case succ

theorem test8 : ∀ n : Nat, n + 0 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => 
    simp [add_succ, ih]

theorem test9 (P Q : Prop) : P → Q → P := by
  intro hp hq
  assumption

theorem test10 (P : Prop) : P → P := by
  intro h
  exact h

theorem test11 (x y : Nat) (h : x = y) : y = x := by
  rw [← h]

theorem test12 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

theorem test13 : 2 + 2 = 4 := by
  simp

theorem test14 (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) : P → R := by
  intro hp
  apply hqr
  apply hpq
  exact hp

theorem test15 (n : Nat) : n * 0 = 0 := by
  induction n <;> simp [*, mul_succ]

theorem test16 : ∃ x : Nat, x > 0 := by
  use 1
  simp

theorem test17 (P : Nat → Prop) (h : ∃ x, P x) : ∃ y, P y := by
  cases h with
  | intro x hx => 
    use x
    exact hx

theorem test18 : 1 ≠ 0 := by
  simp

theorem test19 (h : False) : P := by
  contradiction

theorem test20 (P Q : Prop) (h : P ↔ Q) : Q ↔ P := by
  rw [h]

end Syntax.Tactics.Basic