namespace Syntax.Basic.Comments

-- Single line comment
def x : Nat := 1 -- End of line comment

/- Block comment -/
def y : Nat := 2

/- Multi-line
   block comment
   with multiple lines -/
def z : Nat := 3

/- Nested /- block -/ comments -/
def w : Nat := 4

/-! Module documentation comment
    This is a longer form that can span
    multiple lines and is used for documentation.
-/

/-- Documentation comment for the next declaration
    Can also span multiple lines
-/
def documented : Nat := 5

def foo : Nat := 
  1 + -- comment in expression
  2 + /- another comment -/ 3

-- Unicode in comments: λ ∀ ∃ α β γ 🦀

/- 
   Comments with special characters:
   /* C-style attempt */
   // C++ style attempt
   # Python style
   ; Lisp style
-/

def bar := 42 /- inline block -/ + 1

-- TODO: This is a common pattern
-- FIXME: So is this  
-- NOTE: And this
-- HACK: Unfortunately this too

end Syntax.Basic.Comments