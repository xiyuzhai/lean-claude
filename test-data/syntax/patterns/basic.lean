-- Pattern matching tests

-- Simple patterns
def test1 : Nat → String
  | 0 => "zero"
  | 1 => "one"
  | _ => "many"

-- Variable patterns
def test2 : Nat → Nat
  | x => x + 1

-- Constructor patterns
def head : List α → Option α
  | [] => none
  | x :: _ => some x

def tail : List α → List α
  | [] => []
  | _ :: xs => xs

-- Nested patterns
def second : List α → Option α
  | [] => none
  | [_] => none
  | _ :: x :: _ => some x

-- Tuple patterns
def fst : α × β → α
  | (x, _) => x

def swap : α × β → β × α
  | (x, y) => (y, x)

-- As patterns
def dup : List α → List α × List α
  | l@[] => (l, l)
  | l@(_ :: _) => (l, l)

-- Literal patterns
def isZero : Nat → Bool
  | 0 => true
  | _ => false

def isVowel : Char → Bool
  | 'a' | 'e' | 'i' | 'o' | 'u' => true
  | 'A' | 'E' | 'I' | 'O' | 'U' => true
  | _ => false

-- Pattern guards
def classify : Nat → String
  | n => if n < 10 then "small" else "large"

-- Anonymous constructor patterns
def getCoords : Point → Float × Float
  | ⟨x, y⟩ => (x, y)

-- Inaccessible patterns
def vhead : {n : Nat} → Vector α (n + 1) → α
  | _, Vector.cons x _ => x

-- Pattern matching in let
def test3 (p : Nat × Nat) : Nat :=
  let (x, y) := p
  x + y

def test4 (l : List Nat) : Nat :=
  let x :: _ := l
  x

-- Pattern matching in lambda
def map2 : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: map2 xs ys

-- Recursive patterns
def depth : Tree α → Nat
  | Tree.leaf => 0
  | Tree.node _ l r => 1 + max (depth l) (depth r)

-- Overlapping patterns (first match wins)
def describe : Nat → String
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
  | n => if n < 10 then "small" else "large"

-- Pattern aliases
def test5 : Option Nat → Nat
  | some n => n
  | none => 0