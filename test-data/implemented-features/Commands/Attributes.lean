-- Attribute examples for Lean 4

-- Simple attributes
@[inline]
def simpleInline (x : Nat) : Nat := x + 1

-- Multiple attributes
@[simp, inline]
def multipleAttributes (x : Nat) : Nat := x * 2

-- Attribute with value
@[priority 100]
def highPriority (x : Nat) : Nat := x

-- Attribute with assignment
@[export "myFunction"]
def exportedFunction (x : Nat) : Nat := x + 10

-- Attribute with string value
@[doc "This function squares a number"]
def documented (x : Nat) : Nat := x * x

-- Attribute with parenthesized expression
@[priority (100 + 50)]
def complexPriority (x : Nat) : Nat := x

-- Multiple attribute lists
@[inline] @[simp]
def separateAttributes (x : Nat) : Nat := x + 2

-- Mixed attribute types
@[simp, export "mixed", priority := 75]
def mixedAttributes (x : Nat) : Nat := x - 1

-- Instance with attributes
@[instance, reducible]
def myInstance : Add Nat := inferInstance

-- Structure with attributes
@[ext]
structure AttributedStruct where
  field1 : Nat
  field2 : String

-- Inductive with attributes
@[derive DecidableEq]
inductive AttributedInductive
  | Constructor1 : Nat → AttributedInductive
  | Constructor2 : String → AttributedInductive

-- Theorem with attributes
@[simp]
theorem attributedTheorem (x : Nat) : x + 0 = x := by simp

-- Class with attributes
@[class]
structure AttributedClass (α : Type) where
  op : α → α → α

-- Variable with attributes
@[reducible]
variable (n : Nat)

-- Constant with attributes
@[irreducible]
constant secretConstant : Nat