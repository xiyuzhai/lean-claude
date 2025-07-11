-- Advanced implicit arguments examples

-- Basic implicit arguments
def identity1 {α : Type} (a : α) : α := a

-- Multiple implicit arguments
def pair {α : Type} {β : Type} (a : α) (b : β) : α × β := (a, b)

-- Mixed implicit and explicit arguments
def mixedArgs {α : Type} (x : α) {β : Type} (f : α → β) : β := f x

-- Strict implicit arguments (must be provided)
def strictImplicit {{n : Nat}} (x : Fin n) : Nat := n

-- Instance implicit arguments
def withInstance [Monad m] (x : m α) : m α := x

-- Named instance arguments
def namedInstance [inst : Monad m] (x : m α) : m α := 
  @pure m inst α x

-- Multiple names in one binder
def multipleNames {α β γ : Type} (a : α) (b : β) (c : γ) : α × β × γ := 
  (a, b, c)

-- Auto-implicit arguments (inferred from usage)
def autoImplicit1 (x : α) : α := x  -- α is auto-implicit

-- Complex binder combinations
def complex {α : Type} {{n : Nat}} [Monad m] (x : m (Fin n)) : m α := sorry

-- Implicit arguments in function types
def funcType : {α : Type} → α → α := fun {α} x => x

-- Implicit arguments in lambda
def implicitLambda : Nat → Nat := fun {α : Type} (x : α) => 42

-- Using @ to provide implicit arguments explicitly
def useExplicit (n : Nat) : Nat :=
  @identity1 Nat n

-- Implicit arguments in structures
structure ImplicitStruct {α : Type} where
  value : α
  proof : α = value

-- Implicit arguments in inductive types
inductive ImplicitTree {α : Type} where
  | leaf : α → ImplicitTree
  | node : ImplicitTree → ImplicitTree → ImplicitTree

-- Class with implicit universe
class MyClass {u : Level} (α : Type u) where
  op : α → α → α

-- Instance with implicit arguments
instance {α : Type} [Add α] : MyClass α where
  op := Add.add

-- Implicit arguments in match
def matchImplicit {α : Type} : Option α → Nat
  | none => 0
  | some _ => 1

-- Section variables with implicit arguments
section
  variable {α : Type} {β : Type}
  variable [Monad m]
  
  def sectionFunc (x : m α) (f : α → β) : m β := 
    x >>= (pure ∘ f)
end

-- Type class resolution
def tcResolution [Add α] [Mul α] (x y : α) : α := 
  x + y * x

-- Implicit lambda with type annotation
def implicitTypedLambda : {α : Type} → α → α := 
  fun {α : Type} (x : α) => x

-- Optional implicit arguments
def optionalImplicit {α : Type} (x : α) (y : α := x) : α × α := (x, y)

-- Out parameters in type classes
class HasDefault (α : Type) (default : outParam α) where
  isDefault : α → Bool

-- Implicit arguments with type families
def typeFamily {F : Type → Type} [Functor F] {α β : Type} 
  (f : α → β) (x : F α) : F β := 
  Functor.map f x

-- Combining all binder types
def allBinders 
  (explicitArg : Nat)           -- Explicit
  {implicitArg : Type}          -- Implicit  
  {{strictArg : Nat}}           -- Strict implicit
  [instArg : Monad m]           -- Instance implicit
  : Type := 
  m (Fin strictArg)

-- Pattern matching on implicit arguments
def patternMatch {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + patternMatch xs

-- Dependent implicit arguments
def dependent {α : Type} {P : α → Type} (a : α) (p : P a) : Σ x, P x :=
  ⟨a, p⟩

-- Universe polymorphic implicit arguments
def univPoly {α : Type u} {β : Type v} (f : α → β) (x : α) : β := f x

-- Implicit arguments in type ascriptions
def ascription : Nat := (identity1 : {α : Type} → α → α) 42