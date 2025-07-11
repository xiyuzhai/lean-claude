-- Import common definitions
import Syntax.Prelude

namespace Syntax.Expressions.Match
open TestPrelude

-- Match expression tests

-- Basic match
def test1 (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | x => x + 1

-- Multiple patterns
def test2 (n : Nat) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
  | _ => "many"

-- Pattern matching on multiple values
def test3 (x y : Nat) : Nat :=
  match x, y with
  | 0, 0 => 0
  | 0, y => y
  | x, 0 => x
  | x, y => x + y

-- Constructor patterns
def test4 (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + test4 xs

-- Nested patterns
def test5 (l : List (Nat × Nat)) : Nat :=
  match l with
  | [] => 0
  | (x, y) :: rest => x + y + test5 rest

-- As patterns
def test6 (l : List Nat) : Option (Nat × List Nat) :=
  match l with
  | [] => none
  | x :: xs => some (x, xs)

-- Guards (if let)
def test7 (x : Nat) : Nat :=
  match x with
  | n => if n > 10 then n else 0

-- Wildcard patterns
def test8 (t : Triple Nat) : Nat :=
  match t with
  | ⟨x, _, _⟩ => x
  | ⟨_, y, _⟩ => y
  | ⟨_, _, z⟩ => z

-- Literal patterns
def test9 (c : Char) : String :=
  match c with
  | 'a' => "letter a"
  | 'b' => "letter b"
  | '0' => "digit zero"
  | _ => "other"

-- Variable patterns with type annotations
def test10 (x : Option Nat) : Nat :=
  match x with
  | none => 0
  | some (n : Nat) => n + 1

-- Match with motive
def test11 (n : Nat) : (match n with | 0 => Unit | _ => Nat) :=
  match n with
  | 0 => ()
  | n + 1 => n

-- Dependent match
def test12 (n : Nat) (v : Vector α n) : Option α :=
  match n, v with
  | 0, _ => none
  | n + 1, x :: xs => some x

-- Match with discriminants
def test13 (h : x = 0 ∨ x = 1) : Nat :=
  match h with
  | Or.inl h => 0
  | Or.inr h => 1

-- No confusion patterns
def test14 : (0 : Fin 1) = ⟨0, by simp⟩ := by
  match 0 : Fin 1 with
  | ⟨0, _⟩ => rfl

end Syntax.Expressions.Match