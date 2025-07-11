-- Import common definitions
import Syntax.Prelude

namespace Syntax.Commands.Instances
open TestPrelude

-- Instance tests

-- Basic instance
instance : Add Nat where
  add := Nat.add

-- Named instance
instance natMul : Mul Nat where
  mul := Nat.mul

-- With parameters
instance [Add α] : Add (List α) where
  add := List.append

-- With implicit parameters
instance {α : Type} [Add α] : Add (Option α) where
  add
    | none, x => x
    | x, none => x
    | some x, some y => some (x + y)

-- Dependent instance
instance (n : Nat) : Add (Fin n) where
  add x y := ⟨(x.val + y.val) % n, by sorry⟩

-- Priority
instance (priority := low) : Mul Nat where
  mul := Nat.mul

instance (priority := high) : Mul Nat where
  mul := fun x y => x * y

-- With proof obligations
instance : Monoid Nat where
  one := 1
  mul := (· * ·)
  one_mul := by simp
  mul_one := by simp
  mul_assoc := by simp [Nat.mul_assoc]

-- Conditional instance
instance [Monoid α] : Monoid (Option α) where
  one := some 1
  mul := fun
    | some x, some y => some (x * y)
    | _, _ => none
  one_mul := by intro x; cases x <;> simp
  mul_one := by intro x; cases x <;> simp
  mul_assoc := by intro x y z; cases x <;> cases y <;> cases z <;> simp

-- Type class synthesis
instance [Add α] [Add β] : Add (α × β) where
  add := fun (a₁, b₁) (a₂, b₂) => (a₁ + a₂, b₁ + b₂)

-- Deriving handler
deriving instance Repr for Point
deriving instance DecidableEq for Color

-- Local instance
def foo (x : Nat) : String :=
  let localAdd : Add Nat := ⟨fun x y => x * y⟩  -- weird "addition"
  have : x + x = x * x := by simp [Add.add, localAdd]
  s!"{x} + {x} = {x + x}"

-- Scoped instance
namespace MyNamespace
  scoped instance : Add Nat where
    add := fun x y => x * y + 1
end MyNamespace

-- Default instance
instance (priority := default) : Inhabited Nat where
  default := 0

-- With attributes
@[simp] instance : Zero Nat where
  zero := 0

@[reducible] instance : One Nat where
  one := 1

-- Anonymous instance
instance : ToString Nat := ⟨Nat.repr⟩

-- Instance with where notation
instance : Functor List where
  map := List.map

end Syntax.Commands.Instances