namespace Syntax.Macros.MacroExpansionExamples

-- Macro Expansion Examples
-- This file demonstrates how macros are expanded in Lean 4

-- Example 1: Simple value macro
macro "myNumber" : term => `(42)

-- Usage:
def x : Nat := myNumber
-- Expands to: def x := 42

-- Example 2: Single parameter macro
macro "double" x:term : term => `($x + $x)

-- Usage:
def a : Nat := double 5
-- Expands to: def a := 5 + 5

def b : Nat := double (2 + 3)
-- Expands to: def b := (2 + 3) + (2 + 3)

-- Example 3: Nested macro expansion
macro "triple" x:term : term => `($x + $x + $x)
macro "six_times" x:term : term => `(double (triple $x))

-- Usage:
def c : Nat := six_times 2
-- Expands to: def c := double (triple 2)
-- Which expands to: def c := double (2 + 2 + 2)
-- Which expands to: def c := (2 + 2 + 2) + (2 + 2 + 2)

-- Example 4: Control flow macros
macro "assert!" cond:term : term => `(if $cond then () else panic! "assertion failed")

-- Usage:
def test1 : Unit := assert! (1 < 2)
-- Expands to: def test1 := if (1 < 2) then () else panic! "assertion failed"

-- Example 5: Option macros
macro "some!" x:term : term => `(Option.some $x)
macro "none!" : term => `(Option.none)

-- Usage:
def opt1 : Option Nat := some! 42
-- Expands to: def opt1 := Option.some 42

def opt2 : Option Nat := none!
-- Expands to: def opt2 := Option.none

-- Example 6: Do notation sugar
macro "try!" x:term : term => 
  `(match $x with 
    | some v => v 
    | none => panic! "unwrap failed")

-- Usage:
def unwrapped : Nat := try! (some! 10)
-- Expands to: def unwrapped := match (some! 10) with | some v => v | none => panic! "unwrap failed"
-- Which further expands to: def unwrapped := match (Option.some 10) with | some v => v | none => panic! "unwrap failed"

-- Example 7: Binary operator macros
-- macro:50 x:term " |> " f:term : term => `($f $x)

-- Usage:
def piped : Nat := triple (double 5)
-- Would expand from: 5 |> double |> triple
-- Which expands to: def piped := triple (5 + 5)
-- Which expands to: def piped := (5 + 5) + (5 + 5) + (5 + 5)

-- Example 8: TODO macro
macro "todo!" msg:str : term => `(panic! msg)

-- Usage:
def unimplemented : Nat := todo! "implement this function"
-- Expands to: def unimplemented : Nat := panic! s!"TODO: implement this function"

-- Example 9: Debug helper
macro "dbg!" x:term : term => `(dbgTrace s!"Debug: {$x}" fun _ => $x)

-- Usage:
def traced : Nat := dbg! (1 + 2)
-- Expands to: def traced := dbgTrace s!"Debug: {1 + 2}" fun _ => (1 + 2)

-- Example 10: Simple let binding macro
-- Note: the body needs to reference 'tmp'
macro "with_temp" val:term "as" x:ident "in" body:term : term => `(let $x := $val; $body)

-- Usage:
def with_temp_example : Nat := with_temp 42 as tmp in tmp + 1
-- Expands to: def with_temp_example := let tmp := 42; tmp + 1

-- Test that everything compiles
#check x
#check a
#check b
#check c
#check test1
#check opt1
#check opt2
#check unwrapped
#check piped
#check unimplemented
#check traced
#check with_temp_example

-- Print some values to verify
#eval x -- Should print: 42
#eval a -- Should print: 10
#eval b -- Should print: 10
#eval c -- Should print: 12
#eval opt1 -- Should print: some 42
#eval opt2 -- Should print: none
#eval unwrapped -- Should print: 10
#eval piped -- Should print: 30
#eval traced -- Should print: Debug: 3 \n 3
#eval with_temp_example -- Should print: 43
end Syntax.Macros.MacroExpansionExamples
