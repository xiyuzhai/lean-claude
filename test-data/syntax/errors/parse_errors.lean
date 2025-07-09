-- This file contains intentional parse errors for testing error recovery
-- Each section is marked with what kind of error it contains

-- Missing closing parenthesis
def test1 := (1 + 2

-- Missing closing brace  
def test2 := {x : Nat // x > 0

-- Missing then in if-then-else
def test3 := if x > 0 else 0

-- Missing match arms
def test4 : Nat → Nat :=
  match x with

-- Invalid operator
def test5 := 1 ** 2

-- Missing type after colon
def test6 : := 42

-- Invalid character in identifier
def test@7 := 42

-- Unclosed string
def test8 := "hello world

-- Invalid number literal
def test9 := 0xGHI

-- Missing arrow in lambda
def test10 := λ x x + 1

-- Unexpected keyword
def test11 := def inside

-- Missing definition body
def test12 : Nat :=

-- Invalid pattern
def test13 : Nat → Nat
  | 0 + 1 => 1

-- Mismatched brackets
def test14 := [1, 2, 3}

-- Invalid universe level
def test15 : Type (u +) := Nat

-- Missing comma in list
def test16 := [1 2 3]

-- Invalid attribute
@[invalid_attr] def test17 := 42

-- Unexpected end of input
def test18 := 1 +