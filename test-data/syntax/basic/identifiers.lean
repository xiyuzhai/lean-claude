-- Test various identifier forms

-- Simple identifiers
def x : Nat := 1
def foo : Nat := 2
def fooBar : Nat := 3

-- Unicode identifiers
def α : Type := Nat
def β : Type := Int
def αβγ : Nat := 123

-- Identifiers with numbers
def x1 : Nat := 1
def foo123 : Nat := 123
def bar2baz : Nat := 42

-- Underscores
def _foo : Nat := 1
def foo_ : Nat := 2
def foo_bar : Nat := 3
def _foo_bar_ : Nat := 4

-- Prime notation
def x' : Nat := 1
def x'' : Nat := 2
def foo' : Nat := 3

-- Qualified names
def Foo.bar : Nat := 1
def Foo.Bar.baz : Nat := 2
def A.B.C.d : Nat := 3

-- Reserved-like but valid
def types : Nat := 1  -- 'type' is reserved but 'types' is not
def lets : Nat := 2
def matches : Nat := 3