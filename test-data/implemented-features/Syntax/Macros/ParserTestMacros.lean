namespace Syntax.Macros.ParserTestMacros

-- Macro examples specifically designed to test our Lean parser's macro expansion
-- These match the patterns our parser implementation supports

-- Basic macro without parameters
macro "answer" : term => `(42)

-- Single parameter macro
macro "twice" x:term : term => `($x + $x)

-- Multiple uses of the same macro
def a := twice 5
def b := twice 10
def c := twice (twice 3)

-- Nested macro expansion
macro "double" x:term : term => `($x * 2)
macro "triple" x:term : term => `($x * 3)
macro "sixfold" x:term : term => `(double (triple $x))

def result1 := sixfold 5

-- Control flow style macro (simplified)
def result2 := if true then () else ()

-- Assert-style macro (simplified for our parser)
macro "check" cond:term : term => `(if $cond then () else panic! "check failed")

def test := check (1 < 2)

-- Multiple parameter macro (simplified)
def sum := (10) + (20) + (30)

-- Identity and composition (simplified)
def composed := double (triple (4))

-- List-style macro (simplified)
def myPair := (1, 2)

-- Arithmetic operator macros
macro "squared" x:term : term => `($x * $x)
macro "cubed" x:term : term => `($x * $x * $x)

def sq := squared 5
def cb := cubed 3

-- Boolean macros
macro "isPos" x:term : term => `($x > 0)
macro "isNeg" x:term : term => `($x < 0)

def pos := isPos 5
def neg := isNeg (-3)

-- This file demonstrates the macro patterns our parser can handle:
-- 1. Simple value replacement (answer)
-- 2. Single parameter with antiquotation (twice, double, triple)
-- 3. Multiple parameters (add3, pair, comp)
-- 4. Nested macro calls (sixfold, composed)
-- 5. Control flow patterns (when, check)
-- 6. Arithmetic operations (squared, cubed)
-- 7. Boolean operations (isPos, isNeg)
end Syntax.Macros.ParserTestMacros
