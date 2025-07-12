-- Test module for import functionality
namespace Foo.Bar.Baz

-- A simple definition
def hello : Nat := 42

-- A type definition
def MyNat := Nat

-- A function
def double (n : Nat) : Nat := n + n

-- A theorem
theorem double_is_even (n : Nat) : Even (double n) := sorry

end Foo.Bar.Baz