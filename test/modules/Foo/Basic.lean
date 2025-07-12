-- Basic module with dependencies
import Foo.Bar.Baz

namespace Foo.Basic

-- Re-export some definitions
export Foo.Bar.Baz (hello double)

-- Add our own definition
def triple (n : Nat) : Nat := n + n + n

-- Use imported definition
def six : Nat := double 3

end Foo.Basic