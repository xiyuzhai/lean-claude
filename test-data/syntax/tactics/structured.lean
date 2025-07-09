-- Structured tactic proofs

theorem test_have : ∀ n : Nat, n > 0 → n ≥ 1 := by
  intro n h
  have h1 : n ≠ 0 := by
    intro heq
    rw [heq] at h
    simp at h
  have h2 : n = 0 ∨ n ≥ 1 := by
    cases n
    · left; rfl
    · right; simp
  cases h2
  · contradiction
  · assumption

theorem test_suffices (a b : Nat) : a + b = b + a := by
  suffices h : ∀ x y : Nat, x + y = y + x by
    exact h a b
  intro x y
  induction x with
  | zero => simp
  | succ x ih => simp [succ_add, ih]

theorem test_show : ∃ x : Nat, x > 5 := by
  show ∃ x, x > 5
  use 10
  show 10 > 5
  simp

theorem test_calc (a b c d : Nat) 
    (hab : a = b) (hbc : b = c) (hcd : c = d) : a = d := by
  calc a = b := hab
       _ = c := hbc
       _ = d := hcd

theorem test_calc_with_tactics (n : Nat) : n + n = 2 * n := by
  calc n + n = n * 1 + n * 1 := by simp
       _ = n * (1 + 1) := by rw [← mul_add]
       _ = n * 2 := by simp
       _ = 2 * n := by rw [mul_comm]

theorem test_term_mode : ∀ x : Nat, x + 0 = x := by
  intro x
  show x + 0 = x from by simp

theorem test_focus : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · -- Focus on first goal
    cases h
    assumption
  · -- Focus on second goal
    cases h
    assumption

theorem test_all_goals (P Q R : Prop) : 
    (P → Q → R) → (P ∧ Q → R) := by
  intro h hpq
  cases hpq
  apply h
  all_goals assumption

theorem test_any_goals : (P → Q) ∧ (P → R) → P → Q ∧ R := by
  intro h hp
  cases h with
  | mk hpq hpr =>
    constructor
    any_goals apply hpq
    any_goals apply hpr
    any_goals exact hp

theorem test_repeat : ∀ n : Nat, n + 0 + 0 + 0 = n := by
  intro n
  repeat rw [add_zero]

theorem test_first : ∃ x : Nat, x = x := by
  first
  | use 0; rfl
  | use 1; rfl
  | use 2; rfl

theorem test_try : ∀ n : Nat, n = n := by
  intro n
  try simp  -- May or may not simplify
  rfl      -- But rfl always works

theorem test_by_cases (n : Nat) : n = 0 ∨ n > 0 := by
  by_cases h : n = 0
  · left; exact h
  · right
    cases n
    · contradiction
    · simp