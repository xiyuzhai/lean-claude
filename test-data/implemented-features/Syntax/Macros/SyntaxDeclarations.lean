namespace Syntax.Macros.SyntaxDeclarations

-- Syntax declarations

-- Basic syntax declaration
syntax "test" : term

-- Syntax with parameters
syntax "repeat" num : tactic

-- Syntax with optional components
syntax "optional" (ident)? : term

-- Syntax with repetition
syntax "many" ident* : term
syntax "many1" ident+ : term

-- Syntax with separators
syntax "list" term,* : term
syntax "list1" term,+ : term

-- Syntax with alternatives
syntax "alt" ("foo" <|> "bar") : term

-- Syntax with specific tokens
syntax "bracket" "[" term "]" : term

-- Syntax with precedence
syntax:50 "prec" term : term

-- Syntax with colGt (column greater)
syntax "block" (colGt term)* : term

-- Complex syntax patterns
syntax "for" ident "in" term "do" (colGt tactic)* : tactic

-- Syntax categories (these would need declare_syntax_cat first)
-- syntax myterm : term
-- syntax mytactic : tactic
-- syntax mycommand : command

-- Syntax with attributes
syntax (name := mySyntax) "special" : term

-- Syntax with documentation
/-- A custom syntax for documentation -/
syntax "documented" : term

-- Extended syntax patterns
syntax "match'" term "with" ("|" term "=>" term)* : term

-- Syntax for bindings
syntax "let'" ident ":=" term "in" term : term

-- Syntax with precedence binding
syntax:arg term ":::" term : term
end Syntax.Macros.SyntaxDeclarations
