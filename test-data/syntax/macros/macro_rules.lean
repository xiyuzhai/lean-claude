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
  | `(list $x, $xs,*) => `($x :: list $xs,*)

-- Macro rules for custom tactic
syntax "mytac" (colGt term)* : tactic

macro_rules
  | `(tactic| mytac) => `(tactic| skip)
  | `(tactic| mytac $x) => `(tactic| exact $x)
  | `(tactic| mytac $x $xs*) => `(tactic| apply $x; mytac $xs*)

-- Extending existing syntax
macro_rules
  | `($x + $y + $z) => `(($x + $y) + $z)

-- Complex patterns
syntax "cond" term "?" term ":" term : term

macro_rules
  | `(cond $c ? $t : $f) => `(if $c then $t else $f)