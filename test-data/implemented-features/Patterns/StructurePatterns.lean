-- Structure pattern matching examples

-- Define a simple Point structure
structure Point where
  x : Nat
  y : Nat

-- Define a Color structure
structure Color where
  r : Nat
  g : Nat
  b : Nat

-- Basic structure pattern matching
def getX (p : Point) : Nat :=
  match p with
  | { x := xval, y := _ } => xval

-- Pattern matching with nested structures
structure ColoredPoint where
  pos : Point
  color : Color

def getXFromColored (cp : ColoredPoint) : Nat :=
  match cp with
  | { pos := { x := xval, y := _ }, color := _ } => xval

-- Structure pattern with literal matching
def isOrigin (p : Point) : Bool :=
  match p with
  | { x := 0, y := 0 } => true
  | _ => false

-- Structure pattern with variable binding
def addPoints (p1 p2 : Point) : Point :=
  match (p1, p2) with
  | ({ x := x1, y := y1 }, { x := x2, y := y2 }) => 
    { x := x1 + x2, y := y1 + y2 }

-- Partial structure pattern (not all fields specified)
def isOnXAxis (p : Point) : Bool :=
  match p with
  | { y := 0, .. } => true  -- .. means ignore other fields
  | _ => false

-- Anonymous structure pattern
def processPoint (p : Point) : Nat :=
  match p with
  | { x := a, y := b } => a * 10 + b