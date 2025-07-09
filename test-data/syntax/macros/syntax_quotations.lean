-- Syntax quotations and antiquotations

-- Basic syntax quotation
#check `(1 + 1)
#check `(fun x => x)

-- Quotations with antiquotations
variable (x : Syntax)
#check `($x + 1)
#check `(fun a => $x)

-- Multiple antiquotations
variable (y : Syntax)
#check `($x + $y)

-- Antiquotations with explicit categories
#check `(term| $x:term)
#check `(tactic| exact $x)

-- Nested quotations
#check `(`($x))

-- Quotations in macros
macro "makeAdd" x:term y:term : term => `($x + $y)

-- Pattern matching on syntax
def processSyntax : Syntax → MacroM Syntax
  | `($x + $y) => `($y + $x)  -- swap addition
  | `($x * $y) => `($y * $x)  -- swap multiplication
  | stx => pure stx

-- Syntax matching with multiple patterns
def transformSyntax : Syntax → MacroM Syntax
  | `(∀ $x:ident, $body) => `(∀ $x, transform $body)
  | `(λ $x:ident => $body) => `(λ $x => transform $body)
  | `($f $x) => do
    let f' ← transformSyntax f
    let x' ← transformSyntax x
    `($f' $x')
  | stx => pure stx

-- Quotations with splices
variable (xs : Array Syntax)
#check `(#[$xs,*])

-- Quotations for different categories
#check `(command| def foo := 1)
#check `(tactic| simp [*, foo])
#check `(term| x + y * z)

-- Quotations with identifiers
def mkDef (name : Name) (val : Syntax) : MacroM Syntax := do
  `(def $(mkIdent name) := $val)

-- Complex quotation patterns
macro "genMatch" x:term cs:matchAlt* : term => do
  `(match $x with $cs*)