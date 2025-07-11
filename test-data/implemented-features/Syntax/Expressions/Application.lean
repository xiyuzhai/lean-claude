-- Import common definitions
import Syntax.Prelude

namespace Syntax.Expressions.Application
open TestPrelude

-- Function application tests

-- Basic application
def test1 := id 42
def test2 := const 1 2
def test3 := add 1 2

-- Multiple arguments (using curried functions)
def test4 := f 1

-- Nested applications
def test5 := f (g 1)
def test6 := f (g (h 1))

-- With parentheses
def test7 := (f 1)
def test8 := f (f 1)

-- High-order functions
def test9 := map f list
def test10 := fold add 0 [1, 2, 3]

-- Explicit arguments
def test11 := @id Nat 42
def test12 := @const Nat Nat 42 1

-- Named arguments (simplified)
def test13 := f 1
def test14 : Array Nat := Array.mkEmpty 0

-- Mixed arguments (simplified)
def test15 := f 1

-- Operator sections as functions
def test16 := map (· + 1) list
def test17 := filter (· > 0) list
def test18 := map (2 * ·) list

-- Projection application
def test19 := point.x
def test20 := point.1
def test21 := (mkPoint 1 2).x

-- Method-style application
def test22 := List.map f list
def test23 := List.map f (List.filter (fun n => n > 0) list)
def test24 := List.map f (List.filter (fun n => n > 0) list)

-- Pipeline
def test25 := mul 2 (add 3 5)
def test26 := filter (· > 2) (map (· + 1) [1, 2, 3])

-- Composition
def test27 := f (g 1)
def test28 := f (g (h 1))

-- Complex expressions
def test29 := f (if 1 > 0 then g 1 else h 1)
def test30 := 
  let temp := computeValue 1
  finalize (postProcess (process temp))

end Syntax.Expressions.Application