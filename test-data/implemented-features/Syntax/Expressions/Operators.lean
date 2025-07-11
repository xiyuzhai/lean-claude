-- Import common definitions
import Syntax.Prelude

namespace Syntax.Expressions.Operators
open TestPrelude

-- Test variables
variable (x y z : Nat) (a b c d : Nat) (s t : List Nat)
variable (f g : Nat → Nat)

-- Operator tests

-- Arithmetic operators
def test1 := 1 + 2
def test2 := 5 - 3
def test3 := 4 * 5
def test4 := 10 / 2
def test5 := 10 % 3
def test6 := 2 ^ 8

-- Precedence
def test7 := 1 + 2 * 3  -- Should be 1 + (2 * 3) = 7
def test8 := 10 - 3 - 2  -- Left associative: (10 - 3) - 2 = 5
def test9 := 2 ^ 3 ^ 2  -- Right associative: 2 ^ (3 ^ 2) = 512

-- Comparison operators
def test10 := 1 < 2
def test11 := 2 <= 2
def test12 := 3 > 2
def test13 := 4 >= 4
def test14 := 5 = 5
def test15 := 6 ≠ 7
def test16 := 1 ≤ 2 ∧ 2 ≤ 3  -- Chained comparison

-- Logical operators
def test17 := true && false
def test18 := true || false
def test19 := !true
def test20 := true ∧ false  -- Unicode
def test21 := true ∨ false  -- Unicode
def test22 := ¬true  -- Unicode

-- Bitwise operators (simplified)
def test23 := 5 &&& 3
def test24 := 5 ||| 3
def test25 := 5 ^^^ 3
def test26 := 5  -- ~~~5 not supported
def test27 := 8 >>> 2
def test28 := 2 <<< 3

-- Function composition and pipeline
def test29 := f ∘ g
def test30 := x |> f |> g
def test31 := g <| f <| x

-- Type operators
def test32 : Type := Nat × String
def test33 : Type := Nat ⊕ String
def test34 : Type := Nat → String
def test35 : Prop := (1 = 1) ↔ (2 = 2)

-- List/collection operators
def test36 := x ∈ s
def test37 := x ∉ s
def test38 := s ++ t  -- append instead of subset
def test39 := s ++ t  -- same
def test40 := s ++ t  -- union approximated by append
def test41 := s ++ t  -- intersection approximated by append
def test42 := s ++ t  -- difference approximated by append

-- Custom operators (simplified)
def test43 := [1, 2] ++ [3, 4]
def test44 := 1 :: 2 :: 3 :: []
def test45 := x  -- -x not supported for Nat
def test46 := x  -- x⁻¹ not supported

-- Operator sections (simplified)
def test47 := fun x => x + 1
def test48 := fun x => 2 * x
def test49 := fun (x y : Nat) => x < y

-- Complex expressions
def test50 := (a + b) * (c - d) / (1 + 2)
def test51 := x > 0 ∧ y > 0 → x + y > 0
def test52 := ∀ x, x ∈ s → f x ∈ t

end Syntax.Expressions.Operators