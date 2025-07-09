-- Function application tests

-- Basic application
def test1 := id 42
def test2 := const 1 2
def test3 := add 1 2

-- Multiple arguments
def test4 := f 1 2 3 4 5

-- Nested applications
def test5 := f (g 1) (h 2 3)
def test6 := f (g (h 1))

-- With parentheses
def test7 := (f 1) 2
def test8 := ((f 1) 2) 3

-- High-order functions
def test9 := map f list
def test10 := fold add 0 [1, 2, 3]

-- Explicit arguments
def test11 := @id Nat 42
def test12 := @const Nat String "hello" 42

-- Named arguments
def test13 := f (x := 1) (y := 2)
def test14 := Array.mkEmpty (capacity := 10)

-- Mixed arguments
def test15 := @f Nat (x := 1) 2 (z := 3)

-- Operator sections as functions
def test16 := map (· + 1) list
def test17 := filter (· > 0) list
def test18 := map (2 * ·) list

-- Projection application
def test19 := point.x
def test20 := point.1
def test21 := (mkPoint 1 2).x

-- Method-style application
def test22 := list.map f
def test23 := list.filter p |>.map f
def test24 := (list.filter p).map f

-- Pipeline
def test25 := 5 |> add 3 |> mul 2
def test26 := [1, 2, 3] |> map (· + 1) |> filter (· > 2)

-- Composition
def test27 := (f ∘ g) x
def test28 := (f ∘ g ∘ h) x

-- Complex expressions
def test29 := f (if x > 0 then g x else h x) (y + z)
def test30 := 
  let temp := computeValue x
  process temp |> postProcess |> finalize