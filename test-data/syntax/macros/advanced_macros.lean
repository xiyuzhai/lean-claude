-- Advanced macro examples

-- Recursive macro expansion
macro "list!" xs:term,* : term => do
  let mut result ← `([])
  for x in xs.reverse do
    result ← `($x :: $result)
  pure result

-- Macro generating multiple definitions
macro "genGetSet" decl:ident type:term : command => do
  let getterName := decl.getId.appendAfter "Get"
  let setterName := decl.getId.appendAfter "Set"
  `(variable ($decl : $type)
    def $getterName := $decl
    def $setterName (val : $type) := val)

-- Hygiene in macros
macro "hygienic" : term => do
  `(let x := 42; x + x)  -- x won't clash with outer x

-- Macro with error handling
macro "safe" t:term : term => do
  try
    `(some $t)
  catch _ =>
    `(none)

-- Macro using MonadQuotation
macro "mkPair" x:term y:term : term => do
  let z ← `(temp)
  `(let $z := $x; ($z, $y))

-- Variadic macros
macro "sum!" xs:term* : term => do
  match xs with
  | #[] => `(0)
  | #[x] => pure x
  | _ => xs.foldlM (fun acc x => `($acc + $x)) (xs[0]!)

-- Macro with custom error messages
macro "require" cond:term "msg:" msg:str : term => do
  `(if $cond then () else panic! $msg)

-- Macro transforming syntax tree
macro "swap_args" f:term : term => do
  match f with
  | `($g $x $y) => `($g $y $x)
  | _ => Macro.throwError "swap_args expects a binary application"

-- Conditional macro expansion
macro "ifPos" n:term "then" pos:term "else" neg:term : term => do
  `(if $n > 0 then $pos else $neg)

-- Macro with syntax validation
macro "validIdent" x:ident : term => do
  let name := x.getId
  if name.isAnonymous then
    Macro.throwError "anonymous name not allowed"
  else
    `($(quote name.toString))