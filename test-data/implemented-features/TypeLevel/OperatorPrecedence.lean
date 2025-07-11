-- Operator Precedence Tests
-- This file tests operator precedence and associativity

-- Arithmetic operators
def arith1 := 1 + 2 * 3       -- Should parse as 1 + (2 * 3) = 7
def arith2 := 2 * 3 + 4       -- Should parse as (2 * 3) + 4 = 10
def arith3 := 2 ^ 3 * 4       -- Should parse as (2 ^ 3) * 4 = 32
def arith4 := 2 * 3 ^ 4       -- Should parse as 2 * (3 ^ 4) = 162

-- Associativity
def assoc1 := 1 + 2 + 3       -- Left associative: (1 + 2) + 3
def assoc2 := 2 ^ 3 ^ 2       -- Right associative: 2 ^ (3 ^ 2) = 2 ^ 9 = 512
def assoc3 := 10 - 5 - 2      -- Left associative: (10 - 5) - 2 = 3

-- Comparison operators
def comp1 := 1 + 2 < 3 * 4    -- Should parse as (1 + 2) < (3 * 4)
def comp2 := x = y && a = b   -- Should parse as (x = y) && (a = b)

-- Logical operators
def logic1 := a && b || c     -- Should parse as (a && b) || c
def logic2 := a || b && c     -- Should parse as a || (b && c)
def logic3 := ¬a && b         -- Should parse as (¬a) && b

-- Function application has highest precedence
def app1 := f x + g y         -- Should parse as (f x) + (g y)
def app2 := f x * y           -- Should parse as (f x) * y
def app3 := -f x              -- Should parse as -(f x)

-- Pipe operators have low precedence
def pipe1 := x |> f |> g      -- Left associative: (x |> f) |> g
def pipe2 := f <| g <| x      -- Right associative: f <| (g <| x)
def pipe3 := x + 1 |> f       -- Should parse as (x + 1) |> f

-- Dollar operator (low precedence application)
def dollar1 := f $ g $ h x    -- Right associative: f $ (g $ (h x))
def dollar2 := f $ x + y      -- Should parse as f $ (x + y)

-- Arrow is right associative
def arrow1 : Nat → Nat → Nat  -- Right associative: Nat → (Nat → Nat)
def arrow2 : (Nat → Nat) → Nat

-- List cons is right associative
def list1 := 1 :: 2 :: 3 :: []    -- Right associative: 1 :: (2 :: (3 :: []))

-- Member access has highest precedence
def member1 := obj.field + 1       -- Should parse as (obj.field) + 1
def member2 := obj1.obj2.field     -- Left associative: (obj1.obj2).field

-- Complex expressions
def complex1 := f x + g y * h z
-- Should parse as (f x) + ((g y) * (h z))

def complex2 := a && b || c && d
-- Should parse as (a && b) || (c && d)

def complex3 := -x ^ 2 + y * z
-- Should parse as (-(x ^ 2)) + (y * z)

-- Parentheses override precedence
def paren1 := (1 + 2) * 3         -- Force addition first
def paren2 := 2 ^ (3 * 4)         -- Force multiplication first
def paren3 := (a || b) && c       -- Force OR first

-- Unicode operators
def unicode1 := a ∧ b ∨ c         -- Should parse as (a ∧ b) ∨ c
def unicode2 := f ∘ g ∘ h         -- Right associative: f ∘ (g ∘ h)
def unicode3 := x ≤ y ∧ y ≤ z    -- Should parse as (x ≤ y) ∧ (y ≤ z)