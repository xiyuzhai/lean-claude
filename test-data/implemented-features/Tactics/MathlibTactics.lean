-- Mathlib Tactics
-- This file demonstrates common tactics from Mathlib4

-- ring tactic for commutative ring arithmetic
example (a b c : ℤ) : (a + b) * c = a * c + b * c := by
  ring

example (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring

-- ring_nf for normalization
example (a b : ℤ) : a + b - a = b := by
  ring_nf

-- linarith for linear arithmetic
example (x y z : ℝ) (h1 : x < y) (h2 : y < z) : x < z := by
  linarith

example (a b c : ℚ) (h : a ≤ b) : a + c ≤ b + c := by
  linarith

-- linarith with specific hypotheses
example (x y : ℝ) (h1 : 2*x + y = 4) (h2 : x + 2*y = 5) : x = 1 := by
  linarith [h1, h2]

-- simp_all combines simp with using all hypotheses
example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  simp_all [and_comm]

-- norm_num for numerical computations
example : 2 + 2 = 4 := by
  norm_num

example : (3 : ℝ) / 4 + 1 / 4 = 1 := by
  norm_num

-- field_simp for field arithmetic
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : 
  1 / x + 1 / y = (y + x) / (x * y) := by
  field_simp

-- abel for abelian group problems
example (a b c : ℤ) : a + (b - c) - b = a - c := by
  abel

-- omega for linear integer/natural arithmetic
example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by
  omega

-- tauto for propositional tautologies
example (p q : Prop) : p → (q → p) := by
  tauto

-- aesop for general automation
example (p q r : Prop) (h1 : p → q) (h2 : q → r) (h3 : p) : r := by
  aesop

-- library_search to find lemmas
example (n : ℕ) : n * 0 = 0 := by
  library_search

-- hint for suggestions
example (x : ℝ) : x^2 ≥ 0 := by
  -- hint would suggest: exact sq_nonneg x
  exact sq_nonneg x

-- Combining tactics
example (a b c d : ℝ) (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  linarith

-- Advanced simp usage
example (f : ℕ → ℕ) (h : ∀ x, f x = x + 1) (n : ℕ) : 
  f (f n) = n + 2 := by
  simp only [h]
  ring

-- simp with specific lemmas
example (a b : ℕ) : a + b = b + a := by
  simp only [Nat.add_comm]

-- simp with exclusions
example (x y : ℕ) (h : x = y) : x + 0 = y := by
  simp only [-Nat.add_zero, h]

-- field_simp with assumptions
example (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  x / y / z = x / (y * z) := by
  field_simp

-- Multiple goals with different tactics
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : 
  (p ∧ q) ∧ (q ∧ r) := by
  constructor
  · constructor
    · exact hp
    · exact hq
  · constructor  
    · exact hq
    · exact hr

-- norm_num with inequalities
example : (2 : ℝ) < 3 := by
  norm_num

-- Advanced ring usage
example (n : ℕ) : (n + 1)^3 = n^3 + 3*n^2 + 3*n + 1 := by
  ring

-- Using multiple automation tactics
example (x y : ℝ) (h : x^2 + y^2 = 0) : x = 0 ∧ y = 0 := by
  have hx : x^2 ≥ 0 := sq_nonneg x
  have hy : y^2 ≥ 0 := sq_nonneg y
  have : x^2 = 0 ∧ y^2 = 0 := by linarith
  simp [sq_eq_zero_iff] at this
  exact this