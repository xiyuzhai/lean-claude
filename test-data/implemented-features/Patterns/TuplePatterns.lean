-- Tuple pattern matching examples

-- Simple tuple pattern matching
def first (pair : Nat × Nat) : Nat :=
  match pair with
  | (x, _) => x

def second (pair : Nat × Nat) : Nat :=
  match pair with
  | (_, y) => y

-- Triple pattern matching
def addTriple (triple : Nat × Nat × Nat) : Nat :=
  match triple with
  | (x, y, z) => x + y + z

-- Nested tuple patterns
def processNestedPair (nested : (Nat × Nat) × Nat) : Nat :=
  match nested with
  | ((x, y), z) => x * y + z

-- Tuple pattern with literals
def isOriginPair (pair : Nat × Nat) : Bool :=
  match pair with
  | (0, 0) => true
  | _ => false

-- Mixed patterns in tuples
def describePair (pair : Nat × Nat) : String :=
  match pair with
  | (0, y) => "first is zero, second is " ++ toString y
  | (x, 0) => "first is " ++ toString x ++ ", second is zero"
  | (x, y) => "both non-zero: " ++ toString x ++ ", " ++ toString y

-- Unit type (empty tuple) pattern
def processUnit (unit : Unit) : Nat :=
  match unit with
  | () => 42

-- Tuple pattern with wildcards
def getFirstOfFour (quad : Nat × Nat × Nat × Nat) : Nat :=
  match quad with
  | (x, _, _, _) => x

-- Complex nested tuple patterns
def processComplexTuple (complex : (Nat × Nat) × (Nat × Nat)) : Nat :=
  match complex with
  | ((a, b), (c, d)) => a + b + c + d

-- Tuple pattern in function parameters (direct destructuring)
def swap : Nat × Nat → Nat × Nat
  | (x, y) => (y, x)

-- Multiple tuple patterns
def comparePairs (p1 p2 : Nat × Nat) : Bool :=
  match (p1, p2) with
  | ((x1, y1), (x2, y2)) => x1 + y1 == x2 + y2