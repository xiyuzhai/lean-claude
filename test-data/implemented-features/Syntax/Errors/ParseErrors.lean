namespace Syntax.Errors.ParseErrors

-- This file contains examples of parse errors for testing error recovery
-- Each example is commented out with the actual error shown

/- Missing closing parenthesis
def test1 := (1 + 2
-/
def test1 := (1 + 2) -- Fixed version

/- Missing closing brace  
def test2 := {x : Nat // x > 0
-/
def test2 := {x : Nat // x > 0} -- Fixed version

/- Missing then in if-then-else
def test3 := if x > 0 else 0
-/
def test3 (x : Nat) := if x > 0 then x else 0 -- Fixed version

/- Missing match arms
def test4 : Nat → Nat :=
  match x with
-/
def test4 : Nat → Nat := fun x =>
  match x with
  | 0 => 0
  | n + 1 => n -- Fixed version

/- Invalid operator
def test5 := 1 ** 2
-/
def test5 := 1 ^ 2 -- Fixed version (using power operator)

/- Missing type after colon
def test6 : := 42
-/
def test6 : Nat := 42 -- Fixed version

/- Invalid character in identifier
def test@7 := 42
-/
def test7 := 42 -- Fixed version

/- Unclosed string
def test8 := "hello world
-/
def test8 := "hello world" -- Fixed version

/- Invalid number literal
def test9 := 0xGHI
-/
def test9 := 0xABC -- Fixed version

/- Missing arrow in lambda
def test10 := λ x x + 1
-/
def test10 := λ x => x + 1 -- Fixed version

/- Unexpected keyword
def test11 := def inside
-/
def test11 := 42 -- Fixed version

/- Missing definition body
def test12 : Nat :=
-/
def test12 : Nat := 0 -- Fixed version

/- Invalid pattern - can't match on addition
def test13 : Nat → Nat
  | 0 + 1 => 1
-/
def test13 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n => n -- Fixed version

/- Mismatched brackets
def test14 := [1, 2, 3}
-/
def test14 := [1, 2, 3] -- Fixed version

/- Invalid universe level
def test15 : Type (u +) := Nat
-/
def test15 : Type := Nat -- Fixed version

/- Missing comma in list
def test16 := [1 2 3]
-/
def test16 := [1, 2, 3] -- Fixed version

/- Invalid attribute
@[invalid_attr] def test17 := 42
-/
@[inline] def test17 := 42 -- Fixed version with valid attribute

/- Unexpected end of input
def test18 := 1 +
-/
def test18 := 1 + 2 -- Fixed version

end Syntax.Errors.ParseErrors