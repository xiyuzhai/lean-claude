-- Import common definitions
import Syntax.Prelude

namespace Syntax.Commands.Inductives
open TestPrelude

-- Inductive type tests

-- Basic inductive
inductive Bool where
  | false
  | true

-- With parameters
inductive List (α : Type) where
  | nil
  | cons (head : α) (tail : List α)

-- With indices
inductive Vector (α : Type) : Nat → Type where
  | nil : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

-- Mutual inductive
mutual
  inductive Tree (α : Type) where
    | node : α → Forest α → Tree α

  inductive Forest (α : Type) where
    | nil : Forest α
    | cons : Tree α → Forest α → Forest α
end

-- With explicit universe
inductive Option.{u} (α : Type u) : Type u where
  | none : Option α
  | some : α → Option α

-- Inductive propositions
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ_succ : ∀ n, Even n → Even (n + 2)

-- Inductive families
inductive Eq {α : Type} : α → α → Prop where
  | refl (x : α) : Eq x x

-- With multiple parameters and indices (simplified)
inductive HList : _root_.List Nat → Type where
  | nil : HList (_root_.List.nil)
  | cons : {n : Nat} → {ns : _root_.List Nat} → Nat → HList ns → HList (_root_.List.cons n ns)

-- Nested inductive
inductive Expr where
  | const : Nat → Expr
  | var : String → Expr
  | app : Expr → List Expr → Expr
  | lam : String → Expr → Expr

-- With custom recursor
inductive Acc {α : Type} (r : α → α → Prop) : α → Prop where
  | intro (x : α) : (∀ y, r y x → Acc r y) → Acc r x

-- Quotient inductive (HITs-like)
inductive Quotient {α : Type} (r : α → α → Prop) : Type where
  | mk : α → Quotient r

-- With deriving
inductive Color where
  | red | green | blue
  deriving Repr, DecidableEq

-- Large elimination
inductive Unit : Type where
  | unit : Unit

def Unit.elim {P : Unit → Type} (x : Unit) (h : P unit) : P x :=
  match x with
  | unit => h

-- Inductive with computation rules
inductive W (α : Type) (β : α → Type) where
  | mk (a : α) (f : β a → W α β) : W α β

-- No confusion
inductive Sum (α β : Type) where
  | inl : α → Sum α β
  | inr : β → Sum α β

-- K-like with proof irrelevance
inductive Squash (α : Type) : Prop where
  | mk : α → Squash α

end Syntax.Commands.Inductives