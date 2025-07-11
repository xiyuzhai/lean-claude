-- Import common definitions
import Syntax.Prelude

namespace Syntax.Expressions.LetHave
open TestPrelude

-- Let and have expression tests

-- Basic let
def test1 := 
  let x := 42
  x + 1

-- Multiple let bindings
def test2 :=
  let x := 1
  let y := 2
  let z := 3
  x + y + z

-- Let with type annotation
def test3 :=
  let x : Nat := 42
  let y : String := "hello"
  (x, y)

-- Pattern matching in let
def test4 :=
  let (x, y) := (1, 2)
  x + y

def test5 :=
  let ⟨x, y, z⟩ := point
  x + y + z

-- Dependent let
def test6 :=
  let n := 5
  let arr : Array Nat := Array.mkEmpty n
  arr

-- Recursive let
def test7 :=
  let rec factorial : Nat → Nat
    | 0 => 1
    | n + 1 => (n + 1) * factorial n
  factorial 5

-- Mutual recursion (simplified)
def test8 :=
  let rec isEven : Nat → Bool
    | 0 => true
    | n + 1 => !isEven n
  (isEven 4, isEven 7)

-- Have expressions (for proofs)
def test9 (x : Nat) (h : x > 0) : Nat :=
  have h1 : x ≥ 1 := by sorry
  have h2 : x * x > 0 := by sorry
  x

-- Have with pattern matching (simplified)
def test10 : Nat :=
  have h : 1 > 0 := by sorry
  42

-- Let with complex initialization
def test11 :=
  let data := 
    let temp := computeValue 1
    let processed := process temp
    finalize processed
  data

-- Nested let/have
def test12 :=
  let x := 
    let y := 1
    let z := 2
    y + z
  have _h : x = 3 := by rfl
  x

-- Let with where clause (simplified)
def test13 :=
  let offset := 10
  let f := fun x => x + offset
  f 5

end Syntax.Expressions.LetHave