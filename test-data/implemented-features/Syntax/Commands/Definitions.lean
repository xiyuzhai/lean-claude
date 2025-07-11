-- Import common definitions
import Syntax.Prelude

namespace Syntax.Commands.Definitions
open TestPrelude

-- Definition command tests

-- Basic definitions
def x := 42
def y : Nat := 100
def z : Nat := x + y

-- With parameters
def f (x : Nat) := x + 1
def g (x : Nat) : Nat := x * 2
def h (x y : Nat) := x + y
def k (x : Nat) (y : Nat) := x - y

-- With implicit parameters
def id {α : Type} (x : α) := x
def const {α β : Type} (x : α) (_y : β) := x

-- Mixed parameters
def foo {α : Type} (x : α) {β : Type} (y : β) := (x, y)

-- With type class constraints
def sum {α : Type} [TestPrelude.Add α] (x y : α) := TestPrelude.Add.add x y
def showNat {α : Type} [ToString α] (x : α) : String := toString x

-- Pattern matching definitions
def not : Bool → Bool
  | true => false
  | false => true

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def map {α β : Type} : List α → (α → β) → List β
  | [], _ => []
  | x :: xs, f => f x :: map xs f

-- Recursive definitions
def even : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)

-- Mutual recursion
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

-- With where clause
def sumList (l : List Nat) : Nat :=
  go 0 l
  where
    go acc : List Nat → Nat
      | [] => acc
      | x :: xs => go (acc + x) xs

-- Protected definition
protected def Foo.bar := 42

-- Private definition
private def helper (x : Nat) := x + 1

-- Partial definition
partial def collatz : Nat → Nat
  | 1 => 1
  | n => if n % 2 = 0 then collatz (n / 2) else collatz (3 * n + 1)

-- Noncomputable definition
noncomputable def choice {α : Type} (h : Nonempty α) : α :=
  Classical.choice h

-- With attributes
@[simp] def double (n : Nat) := 2 * n
@[inline] def triple (n : Nat) := 3 * n

-- Abbreviation
abbrev MyNat := Nat
abbrev StateM (σ α : Type) := σ → α × σ

-- With docstring
/-- Computes the length of a list -/
def length {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + length xs

end Syntax.Commands.Definitions