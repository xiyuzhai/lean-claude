-- Test various literal forms

-- Natural numbers
def n1 : Nat := 0
def n2 : Nat := 42
def n3 : Nat := 1234567890

-- Hexadecimal
def h1 : Nat := 0x0
def h2 : Nat := 0xFF
def h3 : Nat := 0xDEADBEEF
def h4 : Nat := 0x123abc

-- Binary
def b1 : Nat := 0b0
def b2 : Nat := 0b1010
def b3 : Nat := 0b11111111

-- Octal  
def o1 : Nat := 0o0
def o2 : Nat := 0o777
def o3 : Nat := 0o123

-- Floating point
def f1 : Float := 0.0
def f2 : Float := 3.14159
def f3 : Float := 1.23e10
def f4 : Float := 1.23e-10
def f5 : Float := 1e20

-- Characters
def c1 : Char := 'a'
def c2 : Char := 'Z'
def c3 : Char := '0'
def c4 : Char := '\n'
def c5 : Char := '\t'
def c6 : Char := '\\'
def c7 : Char := '\''
def c8 : Char := '🦀'  -- Unicode

-- Strings
def s1 : String := ""
def s2 : String := "Hello, World!"
def s3 : String := "Line 1\nLine 2"
def s4 : String := "Tab\there"
def s5 : String := "Quote: \"Hello\""
def s6 : String := "Backslash: \\"
def s7 : String := "Unicode: 🦀 λ ∀ ∃"

-- Raw strings
def r1 : String := r"No \n escape"
def r2 : String := r"C:\Users\path"
def r3 : String := r#"Can use "quotes" freely"#
def r4 : String := r##"Even r#"nested"# ones"##

-- Interpolated strings
def name : String := "Lean"
def i1 : String := s!"Hello, {name}!"
def i2 : String := s!"2 + 2 = {2 + 2}"