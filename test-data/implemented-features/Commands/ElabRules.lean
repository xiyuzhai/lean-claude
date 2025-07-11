namespace Commands.ElabRules

-- Basic elab_rules for term elaboration
elab_rules : term
  | `(myterm) => `(42)

-- Multiple patterns
elab_rules : term
  | `(double $x) => `($x + $x)
  | `(triple $x) => `($x + $x + $x)

-- With attributes
@[term_elab myplus]
elab_rules : term
  | `(myplus $x $y) => `($x + $y)

-- Expected type syntax
elab_rules : term <= expectedType
  | `(mycast $x) => pure x

-- Tactic elaboration rules
elab_rules : tactic
  | `(tactic| mytac) => `(tactic| simp)
  | `(tactic| mytac $x) => `(tactic| simp [$x])

-- Command elaboration rules
elab_rules : command
  | `(command| mycmd $name) => `(command| #check $name)

-- Complex patterns
elab_rules : term
  | `(fold $f [] $init) => `($init)
  | `(fold $f [$x] $init) => `($f $x $init)
  | `(fold $f [$x, $xs,*] $init) => `(fold $f [$xs,*] ($f $x $init))

-- Pattern with type annotation
elab_rules : term
  | `(typed $x : $ty) => `(($x : $ty))

-- Pattern with multiple arguments
elab_rules : term
  | `(apply3 $f $x $y $z) => `($f $x $y $z)

-- Pattern with optional parts (not fully implemented)
-- elab_rules : term
--   | `(maybe $x $[: $ty]?) => ...

-- Pattern with nested syntax
elab_rules : term
  | `(nest ($x + $y)) => `($y + $x)
  | `(nest ($x * $y)) => `($y * $x)

end Commands.ElabRules