-- Import common definitions
import Syntax.Prelude

namespace Syntax.Commands.Instances
open TestPrelude

-- Instance tests

-- Basic instance
instance : TestPrelude.Add Nat where
  add := Nat.add

-- Named instance
instance natMul : TestPrelude.Mul Nat where
  mul := Nat.mul

-- With parameters
instance {α : Type} [TestPrelude.Add α] : TestPrelude.Add (List α) where
  add := List.append

-- With implicit parameters
instance {α : Type} [TestPrelude.Add α] : TestPrelude.Add (Option α) where
  add
    | none, x => x
    | x, none => x
    | some x, some y => some (TestPrelude.Add.add x y)

-- Dependent instance
instance (n : Nat) : TestPrelude.Add (Fin n) where
  add x y := ⟨(x.val + y.val) % n, by sorry⟩

-- Priority
instance (priority := low) : TestPrelude.Mul Nat where
  mul := Nat.mul

instance (priority := high) : TestPrelude.Mul Nat where
  mul := fun x y => x * y

-- With proof obligations (simplified)
instance : TestPrelude.Monoid Nat where
  one := 1
  mul := fun x y => x * y
  one_mul := by sorry
  mul_one := by sorry
  mul_assoc := by sorry

-- Conditional instance (simplified)
instance {α : Type} [TestPrelude.Monoid α] : TestPrelude.Monoid (Option α) where
  one := some TestPrelude.One.one
  mul := fun
    | some x, some y => some (TestPrelude.Mul.mul x y)
    | _, _ => none
  one_mul := by sorry
  mul_one := by sorry
  mul_assoc := by sorry

-- Type class synthesis
instance {α β : Type} [TestPrelude.Add α] [TestPrelude.Add β] : TestPrelude.Add (α × β) where
  add := fun (a₁, b₁) (a₂, b₂) => (TestPrelude.Add.add a₁ a₂, TestPrelude.Add.add b₁ b₂)

-- Deriving handler
deriving instance Repr for Point
deriving instance DecidableEq for Color

-- Local instance
def foo (x : Nat) : String :=
  let localAdd : TestPrelude.Add Nat := ⟨fun x y => x * y⟩  -- weird "addition"
  have : TestPrelude.Add.add x x = x * x := by simp [TestPrelude.Add.add, localAdd]
  s!"{x} + {x} = {TestPrelude.Add.add x x}"

-- Scoped instance
namespace MyNamespace
  scoped instance : TestPrelude.Add Nat where
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