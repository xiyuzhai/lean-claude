-- Scoped Notation and Attributes
-- This file demonstrates scoped notation, attributes, and custom syntax extensions

-- Basic attributes
@[simp] lemma add_zero (n : ℕ) : n + 0 = n := by simp

@[inline] def double (x : ℕ) : ℕ := x + x

@[reducible] def MyNat := ℕ

-- Multiple attributes
@[simp, inline] def triple (x : ℕ) : ℕ := x + x + x

-- Attribute with direction
@[simp ←] lemma zero_add (n : ℕ) : 0 + n = n := by simp

-- Scoped notation without namespace
scoped notation "⟨" x "," y "⟩" => Prod.mk x y

-- Usage of scoped notation
example : ⟨1, 2⟩ = Prod.mk 1 2 := rfl

-- Scoped notation with namespace
namespace Matrix
  scoped[Matrix] notation "⟦" x "⟧" => determinant x
  
  -- Within the namespace, the notation is available
  example (A : Matrix n n ℝ) : ⟦A⟧ = determinant A := rfl
end Matrix

-- Scoped notation with precedence
scoped notation:50 x " ⊕ " y => x + y + 1

example : 2 ⊕ 3 = 6 := by norm_num

-- Local notation (only active in current section)
section LocalNotationExample
  local notation "⟪" x "⟫" => Singleton.mk x
  
  example : ⟪5⟫ = Singleton.mk 5 := rfl
end LocalNotationExample

-- Outside the section, local notation is not available
-- example : ⟪5⟫ = Singleton.mk 5 := rfl  -- This would error

-- Complex scoped notation with multiple parameters
scoped notation "⟨" x "|" p "⟩" => Subtype.mk x p

-- Infix operators with precedence
scoped infix:65 " ⊗ " => HMul.hMul
scoped infixl:70 " ⊘ " => HDiv.hDiv  
scoped infixr:80 " ^ " => HPow.hPow

-- Prefix and postfix notation
scoped prefix:100 "‖" => norm
scoped postfix:max "⁻¹" => inv

-- Macro rules for custom tactics
macro_rules
  | `(tactic| trivial) => `(tactic| first | rfl | simp | omega)

example (x : ℕ) : x = x := by trivial

-- More complex macro rules
macro_rules
  | `(tactic| auto) => `(tactic| simp <;> (first | rfl | omega | linarith))
  | `(tactic| auto using $hyps:term*) => 
      `(tactic| simp [$hyps,*] <;> (first | rfl | omega | linarith))

-- Syntax declarations for custom categories
syntax term:max "begin" tactic,* "end" : term

-- Notation with binding power
notation:65 lhs:65 " ≈ " rhs:66 => Equiv lhs rhs

-- Unicode operators
scoped notation "∑" => Sum
scoped notation "∏" => Product
scoped notation x " ∈ " s => Membership.mem x s

-- Attributes with parameters
@[simp (config := {zeta := false})] 
lemma custom_simp : ∀ x, x + 0 = x := by simp

-- Instance attributes
@[instance] def natAddComm : AddComm ℕ := inferInstance

-- Scoped instances
scoped[Classical] instance : DecidableEq α := Classical.decEq

-- Combining scoped notation with attributes
@[simp]
scoped notation:arg "√" x => Real.sqrt x

-- Pattern matching in macro rules
macro_rules
  | `(tactic| solve_by_elim) => `(tactic| repeat (first | assumption | apply _))

-- Advanced macro with multiple patterns
macro_rules
  | `(term| list[$xs:term,*]) => `(term| [$xs,*])
  | `(term| list[]) => `(term| [])

example : list[1, 2, 3] = [1, 2, 3] := rfl

-- Syntax with repetitions
syntax "repeat" tactic "until" term : tactic

-- Optional syntax elements
syntax "try"? tactic : tactic

-- Custom binders in notation
scoped notation "∀'" binders ", " r:(scoped p => p) => Forall r

-- Mixfix notation
scoped notation "if " c " then " t " else " e => ite c t e

-- Complex attribute applications
section AttributeExamples
  variable (α : Type*) [Monoid α]
  
  @[to_additive] 
  lemma mul_one (a : α) : a * 1 = a := by simp
  
  @[simp, norm_cast]
  lemma cast_add (n m : ℕ) : ↑(n + m) = (↑n : ℤ) + ↑m := by simp
end AttributeExamples