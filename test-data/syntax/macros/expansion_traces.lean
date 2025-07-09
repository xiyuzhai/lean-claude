-- Macro Expansion Trace Examples
-- This file shows step-by-step macro expansion

-- === Example 1: Simple Arithmetic Macro ===
macro "twice" x:term : term => `($x + $x)

def example1 : Nat := twice 42

-- Expansion trace:
-- Step 1: twice 42
-- Step 2: 42 + 42
-- Final AST: (BinOp 42 + 42)

-- === Example 2: Nested Macro Expansion ===
macro "quad" x:term : term => `(twice (twice $x))

def example2 : Nat := quad 10

-- Expansion trace:
-- Step 1: quad 10
-- Step 2: twice (twice 10)
-- Step 3: twice (10 + 10)
-- Step 4: (10 + 10) + (10 + 10)
-- Final AST: (BinOp (BinOp 10 + 10) + (BinOp 10 + 10))

-- === Example 3: Complex Expression ===
macro "double" x:term : term => `($x * 2)
macro "triple" x:term : term => `($x * 3)

def example3 : Nat := double (triple 5)

-- Expansion trace:
-- Step 1: double (triple 5)
-- Step 2: double (5 * 3)
-- Step 3: (5 * 3) * 2
-- Final AST: (BinOp (BinOp 5 * 3) * 2)

-- === Example 4: Control Flow Macro ===
macro "unless" cond:term "then" body:term : term => `(if !$cond then $body else ())

def example4 : Unit := unless false then ()

-- Expansion trace:
-- Step 1: unless false then ()
-- Step 2: if !false then () else ()
-- Final AST: (If (UnaryOp ! false) () Unit.unit)

-- === Example 5: Multiple Parameter Macro ===
macro "clamp" x:term "between" low:term "and" high:term : term => 
  `(if $x < $low then $low else if $x > $high then $high else $x)

def example5 : Nat := clamp 150 between 0 and 100

-- Expansion trace:
-- Step 1: clamp 150 between 0 and 100
-- Step 2: if 150 < 0 then 0 else if 150 > 100 then 100 else 150
-- Final AST: (If (BinOp 150 < 0) 0 (If (BinOp 150 > 100) 100 150))

-- === Example 6: Hygienic Macro Expansion ===
macro "let_twice" name:ident "=" val:term "in" body:term : term =>
  `(let $name := $val; let $name := $name + $name; $body)

def example6 : Nat := let_twice x = 5 in x * 2

-- Expansion trace:
-- Step 1: let_twice x = 5 in x * 2
-- Step 2: let x := 5; let x := x + x; x * 2
-- Note: The second 'x' shadows the first, but hygiene ensures correct binding
-- Final AST: (Let x 5 (Let x (BinOp x + x) (BinOp x * 2)))

-- === Example 7: Quotation with Multiple Antiquotations ===
macro "swap_args" f:term x:term y:term : term => `($f $y $x)

def div (x y : Nat) : Nat := x / y
def div_swapped : Nat := swap_args div 2 10

-- Expansion trace:
-- Step 1: swap_args div 2 10
-- Step 2: div 10 2
-- Final AST: (App (App div 10) 2)

-- === Example 8: Simple Repetition Macro ===
macro "three_times" body:term : term => `($body; $body; $body)

def print3 : Unit := three_times (dbgTrace "hello" fun _ => ())

-- Expansion trace:
-- Step 1: three_times (dbgTrace "hello" fun _ => ())
-- Step 2: (dbgTrace "hello" fun _ => ()); (dbgTrace "hello" fun _ => ()); (dbgTrace "hello" fun _ => ())

-- === Example 9: Pattern Matching in Macros ===
macro "match_option" opt:term "with" "|" "some" x:ident "=>" some_case:term "|" "none" "=>" none_case:term : term =>
  `(match $opt with | Option.some $x => $some_case | Option.none => $none_case)

def example9 : Nat := match_option (Option.some 42) with | some x => x + 1 | none => 0

-- Expansion trace:
-- Step 1: match_option (Option.some 42) with | some x => x + 1 | none => 0
-- Step 2: match (Option.some 42) with | Option.some x => x + 1 | Option.none => 0
-- Final AST: (Match (App Option.some 42) [(Pattern Option.some x) (BinOp x + 1)] [(Pattern Option.none) 0])

-- === Example 10: Chained Macro Application ===
macro "increment" x:term : term => `($x + 1)
macro "decrement" x:term : term => `($x - 1)
macro "id" x:term : term => `(increment (decrement $x))

def example10 : Nat := id 100

-- Expansion trace:
-- Step 1: id 100
-- Step 2: increment (decrement 100)
-- Step 3: increment (100 - 1)
-- Step 4: (100 - 1) + 1
-- Final AST: (BinOp (BinOp 100 - 1) + 1)

-- Verify all examples compile
#check example1
#check example2
#check example3
#check example4
#check example5
#check example6
#check div_swapped
#check print3
#check example9
#check example10

-- Test evaluations
#eval example1 -- Should be: 84
#eval example2 -- Should be: 40
#eval example3 -- Should be: 30
#eval example5 -- Should be: 100
#eval example6 -- Should be: 20
#eval div_swapped -- Should be: 5
#eval example9 -- Should be: 43
#eval example10 -- Should be: 100