-- Advanced Tactics and Combinators
-- This file demonstrates advanced tactic features in Lean 4

-- Tactic combinators
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- repeat combinator
example (a b c : Nat) : a + 0 + 0 = a := by
  repeat rw [Nat.add_zero]

-- try combinator
example (p : Prop) (hp : p) : p := by
  try simp  -- This might not do anything, but won't fail
  exact hp

-- first combinator - tries tactics until one succeeds
example (p : Prop) (hp : p) : p := by
  first | rfl | exact hp | assumption

-- all_goals combinator
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  constructor
  constructor
  all_goals assumption

-- focus combinator
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · focus exact hp
  · exact hq

-- Structured proofs with have
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  have h3 : a = b := h1
  have h4 : b = c := h2
  rw [h3, h4]

-- Structured proofs with let
example (n : Nat) : n + n = 2 * n := by
  let m := n
  have : m + m = 2 * m := by simp [Nat.two_mul]
  exact this

-- Structured proofs with show
example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  have hp : p := h.1
  have hq : q := h.2
  show q ∧ p
  exact ⟨hq, hp⟩

-- calc mode for equational reasoning
example (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  calc a = b := h1
       _ = c := h2
       _ = d := h3

-- conv mode for conversion tactics
example (a b : Nat) : a + b = b + a := by
  conv => 
    lhs
    rw [Nat.add_comm]

-- Pattern matching in tactics
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- Named pattern matching
example (n : Nat) : n = 0 ∨ ∃ m, n = m + 1 := by
  cases n with
  | zero => left; rfl
  | succ m => right; exact ⟨m, rfl⟩

-- Induction with pattern matching
example (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [Nat.add_zero]

-- Multiple goals with different tactics
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : (p ∧ q) ∧ r := by
  constructor
  · constructor
    · assumption  -- finds hp
    · assumption  -- finds hq
  · assumption    -- finds hr

-- Using custom tactics (user-defined)
example (p : Prop) (hp : p) : p := by
  -- In real Lean, you could define custom tactics
  exact hp

-- Tactic macros and notation
example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  -- Lean 4 allows defining tactic macros
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

-- guard tactics for assertions
example (n : Nat) (h : n = 5) : n = 5 := by
  guard_hyp h : n = 5  -- Check that h has the expected type
  guard_target = (n = 5)  -- Check the goal
  exact h

-- fail_if_success for negative tests
example (p : Prop) : p → p := by
  intro hp
  -- fail_if_success { rfl }  -- This would fail if rfl succeeded
  exact hp

-- suffices tactic
example (a b : Nat) (h : a < b) : a ≤ b := by
  suffices h : a < b ∨ a = b by
    cases h with
    | inl h => exact Nat.le_of_lt h
    | inr h => exact Nat.le_of_eq h
  left
  exact h

-- any_goals combinator
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  constructor
  constructor
  any_goals { exact hp }
  exact hq