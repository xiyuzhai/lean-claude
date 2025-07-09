-- Elaboration and macro interaction

-- Elaborator that uses macros
elab "elaborate" x:term : term => do
  let stx ← `($x + 1)
  Lean.Elab.Term.elabTerm stx none

-- Custom elaborator with macro expansion
elab "customElab" x:term : term => do
  let expanded ← Lean.expandMacros x
  Lean.Elab.Term.elabTerm expanded none

-- Mixing macros and elaborators
macro "stage1" x:term : term => `(stage2 $x)
elab "stage2" x:term : term => do
  let doubled ← `($x + $x)
  Lean.Elab.Term.elabTerm doubled none

-- Syntax transformer
elab "transform" x:term : term => do
  let transformed ← match x with
    | `($a + $b) => `($b + $a)
    | `($a * $b) => `($b * $a)
    | _ => pure x
  Lean.Elab.Term.elabTerm transformed none

-- Macro with elaboration-time computation
elab "compute" n:num : term => do
  let n' := n.toNat
  let result := n' * n'
  let stx ← `($(quote result))
  Lean.Elab.Term.elabTerm stx none

-- Tactic macro with elaboration
macro "custom_simp" : tactic => `(tactic| simp [*, -one_mul])

-- Command elaborator using macros
elab "defAlias" name:ident orig:ident : command => do
  Lean.Elab.Command.elabCommand (← `(def $name := $orig))

-- Syntax quotation in elaborator
elab "quoted" : term => do
  let stx ← `(fun x => x + 1)
  let quoted ← `(Syntax.node `anon #[$(quote stx.getKind.toString)])
  Lean.Elab.Term.elabTerm quoted none

-- Pattern matching in elaborators
elab "matchElab" x:term : term => do
  match x with
  | `($f $a $b) => Lean.Elab.Term.elabTerm (← `($f $b $a)) none
  | `(fun $x => $body) => Lean.Elab.Term.elabTerm (← `(λ $x => elaborate $body)) none
  | _ => Lean.Elab.Term.elabTerm x none