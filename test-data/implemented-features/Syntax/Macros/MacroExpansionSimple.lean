namespace Syntax.Macros.MacroExpansionSimple

-- Simple Macro Expansion Examples that compile in Lean 4
-- This file demonstrates basic macro expansions

-- Example 1: Simple value macro
macro "myNumber" : term => `(42)

def x : Nat := myNumber
#check x
#eval x -- Should print: 42

-- Example 2: Single parameter macro
macro "double" x:term : term => `($x + $x)

def a : Nat := double 5
def b : Nat := double (2 + 3)
#check a
#check b
#eval a -- Should print: 10
#eval b -- Should print: 10

-- Example 3: Nested macro expansion
macro "triple" x:term : term => `($x + $x + $x)
macro "sixTimes" x:term : term => `(double (triple $x))

def c : Nat := sixTimes 2
#check c
#eval c -- Should print: 12

-- Example 4: Simple conditional macro
macro "isZero" x:term : term => `($x = 0)

def test1 : Bool := isZero 0
def test2 : Bool := isZero 5
#check test1
#check test2
#eval test1 -- Should print: true
#eval test2 -- Should print: false

-- Example 5: Option macros (simplified)
macro "mkSome" x:term : term => `(Option.some $x)
macro "mkNone" : term => `(Option.none)

def opt1 : Option Nat := mkSome 42
def opt2 : Option Nat := mkNone
#check opt1
#check opt2
#eval opt1 -- Should print: some 42
#eval opt2 -- Should print: none

-- Example 6: Simple arithmetic macro
macro "square" x:term : term => `($x * $x)

def sq : Nat := square 7
#check sq
#eval sq -- Should print: 49

-- Example 7: Combining macros
macro "squareDouble" x:term : term => `(square (double $x))

def sd : Nat := squareDouble 3
#check sd
#eval sd -- Should print: 36

-- Example 8: Simple identity macro
macro "id" x:term : term => `($x)

def idTest : Nat := id 100
#check idTest
#eval idTest -- Should print: 100

-- Example 9: Add one macro
macro "inc" x:term : term => `($x + 1)

def incremented : Nat := inc (inc (inc 0))
#check incremented
#eval incremented -- Should print: 3

-- Example 10: Boolean macros
macro "myTrue" : term => `(true)
macro "myFalse" : term => `(false)
macro "myNot" x:term : term => `(!$x)

def bool1 : Bool := myTrue
def bool2 : Bool := myFalse
def bool3 : Bool := myNot myTrue
#check bool1
#check bool2
#check bool3
#eval bool1 -- Should print: true
#eval bool2 -- Should print: false
#eval bool3 -- Should print: false

-- Summary: All macros expand correctly
-- The expanded code is type-checked and evaluated
end Syntax.Macros.MacroExpansionSimple
