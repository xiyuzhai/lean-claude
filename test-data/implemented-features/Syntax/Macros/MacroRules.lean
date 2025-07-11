namespace Syntax.Macros.MacroRules

-- Macro rules for pattern matching

-- Define a syntax category
syntax "myterm" : term

-- Basic macro_rules
macro_rules
  | `(myterm) => `(42)

-- Multiple rules
macro_rules
  | `(myterm) => `(42)
  | `(myterm $x) => `($x + 1)
  | `(myterm $x $y) => `($x + $y)

-- Macro rules with patterns
syntax "list" (term,*) : term

macro_rules
  | `(list) => `([])
  | `(list $x) => `([$x])

-- Macro rules for custom tactic
syntax "mytac" (colGt term)* : tactic

macro_rules
  | `(tactic| mytac) => `(tactic| skip)
  | `(tactic| mytac $x) => `(tactic| exact $x)

-- Extending existing syntax (simplified)
-- macro_rules
  -- | `($x + $y + $z) => `($x + $y + $z)

-- Complex patterns (simplified)
syntax "simple" term : term

macro_rules
  | `(simple $x) => `($x)
end Syntax.Macros.MacroRules
