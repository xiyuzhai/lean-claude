namespace Syntax.Macros.BasicMacros

-- Basic macro definitions

-- Simple macro without parameters
macro "myNumber" : term => `(42)

-- Macro with a single parameter
macro "double" x:term : term => `($x + $x)

-- Macro with multiple parameters
macro "triple" x:term : term => `($x + $x + $x)

-- Macro with precedence
macro (priority := high) "high_prec" : term => `(1)

-- Macro with attributes
@[simp] macro "simp_macro" : term => `(0)

-- String pattern macros
macro "∀∀" xs:ident* "," b:term : term => do
  let mut body := b
  for x in xs.reverse do
    body ← `(∀ $x:ident, $body)
  pure body

-- Macro with category specification
macro "myTactic" : tactic => `(simp)

-- Named macro
macro (name := myAtom) "atom" : term => `(42)

-- Another named macro
macro (name := myLeading) "lead" : term => `(100)
end Syntax.Macros.BasicMacros
