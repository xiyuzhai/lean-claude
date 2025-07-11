-- Universe polymorphism examples

-- Basic universe declarations
universe u v w
universe u₁ u₂ u₃

-- Using universe variables in types
def id1 {α : Type u} (a : α) : α := a
def id2 {α : Type v} (a : α) : α := a
def id3 {α : Sort u} (a : α) : α := a

-- Type* notation (universe to be inferred)
def id4 {α : Type*} (a : α) : α := a

-- Sort levels
def sortExample1 : Sort 0 := Nat
def sortExample2 : Sort 1 := Type
def sortExample3 : Sort (u+1) := Type u

-- Type levels
def typeExample1 : Type 0 := Nat
def typeExample2 : Type 1 := Type 0
def typeExample3 : Type u := List (Type v)

-- Prop is Sort 0
def propExample : Prop := True

-- Universe max and imax
def maxExample {α : Type (max u v)} {β : Type u} {γ : Type v} : Type (max u v) := α

def imaxExample {p : Prop} {α : Type u} : Sort (imax 1 u) := 
  if p then α else Unit

-- Function types with universe polymorphism
def funcType1 : Type u → Type v → Type (max u v) := 
  fun α β => α × β

def funcType2 {α : Type u} {β : Type v} : Type (max u v) := 
  α → β

-- Polymorphic structures
structure Prod' (α : Type u) (β : Type v) : Type (max u v) where
  fst : α
  snd : β

-- Inductive types with universes
inductive Tree (α : Type u) : Type u
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

-- Universe constraints in classes
class Container (C : Type u → Type v) where
  empty : {α : Type u} → C α
  insert : {α : Type u} → α → C α → C α

-- Higher-order types
def higherOrder : (Type u → Type v) → Type (max u v) :=
  fun F => F Nat

-- Universe levels in definitions
def compose {α : Type u} {β : Type v} {γ : Type w} 
  (g : β → γ) (f : α → β) : α → γ :=
  fun x => g (f x)

-- Explicit universe annotations
def explicitUniv : List.{u} (Type v) → Type (max u (v+1)) :=
  fun _ => Type v

-- Universe polymorphic constants
constant myConst : {u : Level} → Type u → Type u

-- Sort* notation
def sortStar {α : Sort*} (a : α) : α := a

-- Mixed universe levels
def mixed {α : Type u} {β : Sort v} {γ : Type*} : Type* :=
  α → β → γ

-- Complex universe expressions
def complex : Type (max u (v+1)) → Type (max (u+2) v) :=
  fun _ => Unit

-- Universe-polymorphic recursion
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs

-- Auto-implicit universes (when enabled)
def autoImplicit (α : Type _) (a : α) : α := a

-- Universe levels in match expressions
def matchUniv {α : Type u} : Option α → Type u
  | none => Unit
  | some _ => α

-- Dependent types with universes
def dependent {α : Type u} (P : α → Type v) (a : α) : Type v := P a

-- Universe constraints in theorems
theorem univTheorem {α : Type u} {β : Type v} : 
  (α → β) → Type (max u v) :=
  fun _ => α × β