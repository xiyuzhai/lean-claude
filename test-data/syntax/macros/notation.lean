-- Notation definitions

-- Basic notation
notation "⟨" x "," y "⟩" => Prod.mk x y

-- Notation with precedence
notation:50 x " ⊕ " y => x + y + 1

-- High precedence notation
notation:max x "²" => x * x

-- Left associative notation
infixl:65 " ⊗ " => HMul.hMul

-- Right associative notation
infixr:35 " ⇒ " => implies

-- Notation with explicit precedence
notation:70 "√" x => Float.sqrt x

-- Prefix notation
prefix:100 "¬¬" => not ∘ not

-- Postfix notation
postfix:max "⁺" => Nat.succ

-- Mixfix notation
notation "⟦" x "⟧" => interpret x

-- Complex notation patterns
notation "∑ " x " ∈ " s ", " f => s.sum f
notation "∏ " x " ∈ " s ", " f => s.prod f

-- Scoped notation
scoped notation "𝔽" => Fin

-- Local notation (in a section)
section
  local notation "⊙" => myOperation
  
  def myOperation (x y : Nat) := x * y + x + y
end

-- Unicode-heavy notation
notation "∀ε>0" => ∀ ε > 0
notation "∃δ>0" => ∃ δ > 0