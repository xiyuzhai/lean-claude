-- Import common definitions
import Syntax.Prelude

namespace Syntax.Commands.Structures
open TestPrelude

-- Structure and class tests

-- Basic structure
structure Point where
  x : Float
  y : Float

-- With default values
structure Point3D where
  x : Float := 0.0
  y : Float := 0.0
  z : Float := 0.0

-- With constructor syntax
structure Person where
  name : String
  age : Nat

-- With inheritance
structure ColoredPoint extends Point where
  color : Color

-- Multiple inheritance
structure NamedColoredPoint extends ColoredPoint, Named where
  id : Nat

-- With parameters
structure Vector (α : Type) (n : Nat) where
  data : Array α
  size_eq : data.size = n

-- With implicit parameters
structure Functor (F : Type → Type) {α β : Type} where
  map : (α → β) → F α → F β

-- Type class
class Add (α : Type) where
  add : α → α → α

class Mul (α : Type) where
  mul : α → α → α

-- Type class with laws
class Monoid (α : Type) extends Mul α where
  one : α
  one_mul : ∀ x : α, mul one x = x
  mul_one : ∀ x : α, mul x one = x
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)

-- With notation
class Group (α : Type) extends Monoid α where
  inv : α → α
  mul_left_inv : ∀ x : α, mul (inv x) x = one

-- Structure with private fields
structure Config where
  server : String
  port : Nat
  debug : Bool := false

-- With auto-generated projections
structure Rect where
  width : Float
  height : Float
  deriving Repr

-- Dependent structure
structure Sigma {α : Type} (β : α → Type) where
  fst : α
  snd : β fst

-- Record update syntax usage
def movePoint (p : Point) (dx dy : Float) : Point :=
  { p with x := p.x + dx, y := p.y + dy }

-- Anonymous constructor syntax
def origin : Point := ⟨0, 0⟩
def unitSquare : Rect := ⟨1, 1⟩

-- Pattern matching on structures
def distance (p : Point) : Float :=
  match p with
  | ⟨x, y⟩ => sqrt (x * x + y * y)

-- Extending structures inline
def special : Point := {
  x := 1.0
  y := 2.0
  : Point
}

end Syntax.Commands.Structures