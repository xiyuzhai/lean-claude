//! Operator precedence and associativity for Lean 4

use std::collections::HashMap;

use once_cell::sync::Lazy;

/// Precedence level for operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Precedence(pub u32);

impl Precedence {
    pub const MIN: Precedence = Precedence(0);
    pub const ARROW: Precedence = Precedence(25);
    pub const OR: Precedence = Precedence(30);
    pub const AND: Precedence = Precedence(35);
    pub const CMP: Precedence = Precedence(50);
    pub const ADD: Precedence = Precedence(65);
    pub const MUL: Precedence = Precedence(70);
    pub const POW: Precedence = Precedence(80);
    pub const COMPOSE: Precedence = Precedence(90);
    pub const MAX: Precedence = Precedence(1024);

    /// Get the next precedence level
    pub fn next(self) -> Precedence {
        Precedence(self.0 + 1)
    }
}

/// Associativity of operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
    None,
}

/// Information about an operator
#[derive(Debug, Clone)]
pub struct OperatorInfo {
    pub symbol: String,
    pub precedence: Precedence,
    pub associativity: Associativity,
}

// Static operator tables
static BINARY_OPERATORS: Lazy<HashMap<String, OperatorInfo>> = Lazy::new(|| {
    let mut ops = HashMap::new();

    // Logical operators
    ops.insert(
        "||".to_string(),
        OperatorInfo {
            symbol: "||".to_string(),
            precedence: Precedence(20),
            associativity: Associativity::Right,
        },
    );
    ops.insert(
        "&&".to_string(),
        OperatorInfo {
            symbol: "&&".to_string(),
            precedence: Precedence(35),
            associativity: Associativity::Right,
        },
    );
    ops.insert(
        "∨".to_string(),
        OperatorInfo {
            symbol: "∨".to_string(),
            precedence: Precedence(30),
            associativity: Associativity::Right,
        },
    );
    ops.insert(
        "∧".to_string(),
        OperatorInfo {
            symbol: "∧".to_string(),
            precedence: Precedence(35),
            associativity: Associativity::Right,
        },
    );

    // Comparison operators
    ops.insert(
        "=".to_string(),
        OperatorInfo {
            symbol: "=".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "==".to_string(),
        OperatorInfo {
            symbol: "==".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "≠".to_string(),
        OperatorInfo {
            symbol: "≠".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "!=".to_string(),
        OperatorInfo {
            symbol: "!=".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "<".to_string(),
        OperatorInfo {
            symbol: "<".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        ">".to_string(),
        OperatorInfo {
            symbol: ">".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "≤".to_string(),
        OperatorInfo {
            symbol: "≤".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "≥".to_string(),
        OperatorInfo {
            symbol: "≥".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "<=".to_string(),
        OperatorInfo {
            symbol: "<=".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        ">=".to_string(),
        OperatorInfo {
            symbol: ">=".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );

    // Arrow operators
    ops.insert(
        "->".to_string(),
        OperatorInfo {
            symbol: "->".to_string(),
            precedence: Precedence(25),
            associativity: Associativity::Right,
        },
    );
    ops.insert(
        "→".to_string(),
        OperatorInfo {
            symbol: "→".to_string(),
            precedence: Precedence(25),
            associativity: Associativity::Right,
        },
    );
    ops.insert(
        "=>".to_string(),
        OperatorInfo {
            symbol: "=>".to_string(),
            precedence: Precedence(25),
            associativity: Associativity::Right,
        },
    );

    // Type ascription
    ops.insert(
        ":".to_string(),
        OperatorInfo {
            symbol: ":".to_string(),
            precedence: Precedence(20),
            associativity: Associativity::None,
        },
    );

    // List cons
    ops.insert(
        "::".to_string(),
        OperatorInfo {
            symbol: "::".to_string(),
            precedence: Precedence(55),
            associativity: Associativity::Right,
        },
    );

    // Append
    ops.insert(
        "++".to_string(),
        OperatorInfo {
            symbol: "++".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Right,
        },
    );

    // Arithmetic operators
    ops.insert(
        "+".to_string(),
        OperatorInfo {
            symbol: "+".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "-".to_string(),
        OperatorInfo {
            symbol: "-".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "*".to_string(),
        OperatorInfo {
            symbol: "*".to_string(),
            precedence: Precedence(70),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "/".to_string(),
        OperatorInfo {
            symbol: "/".to_string(),
            precedence: Precedence(70),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "%".to_string(),
        OperatorInfo {
            symbol: "%".to_string(),
            precedence: Precedence(70),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "^".to_string(),
        OperatorInfo {
            symbol: "^".to_string(),
            precedence: Precedence(80),
            associativity: Associativity::Right,
        },
    );

    // Function composition
    ops.insert(
        "∘".to_string(),
        OperatorInfo {
            symbol: "∘".to_string(),
            precedence: Precedence(90),
            associativity: Associativity::Right,
        },
    );
    ops.insert(
        "○".to_string(),
        OperatorInfo {
            symbol: "○".to_string(),
            precedence: Precedence(90),
            associativity: Associativity::Right,
        },
    );

    // Mathematical set operations
    ops.insert(
        "∈".to_string(),
        OperatorInfo {
            symbol: "∈".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "∉".to_string(),
        OperatorInfo {
            symbol: "∉".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "⊂".to_string(),
        OperatorInfo {
            symbol: "⊂".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "⊃".to_string(),
        OperatorInfo {
            symbol: "⊃".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "⊆".to_string(),
        OperatorInfo {
            symbol: "⊆".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "⊇".to_string(),
        OperatorInfo {
            symbol: "⊇".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "∩".to_string(),
        OperatorInfo {
            symbol: "∩".to_string(),
            precedence: Precedence(70),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "∪".to_string(),
        OperatorInfo {
            symbol: "∪".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "∖".to_string(),
        OperatorInfo {
            symbol: "∖".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "△".to_string(),
        OperatorInfo {
            symbol: "△".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Left,
        },
    );

    // Mathematical quantifiers and logical symbols
    ops.insert(
        "⇒".to_string(),
        OperatorInfo {
            symbol: "⇒".to_string(),
            precedence: Precedence(25),
            associativity: Associativity::Right,
        },
    );
    ops.insert(
        "⇔".to_string(),
        OperatorInfo {
            symbol: "⇔".to_string(),
            precedence: Precedence(20),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "↔".to_string(),
        OperatorInfo {
            symbol: "↔".to_string(),
            precedence: Precedence(20),
            associativity: Associativity::None,
        },
    );

    // Mathematical equivalence and congruence
    ops.insert(
        "≈".to_string(),
        OperatorInfo {
            symbol: "≈".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "≃".to_string(),
        OperatorInfo {
            symbol: "≃".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "≅".to_string(),
        OperatorInfo {
            symbol: "≅".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "≡".to_string(),
        OperatorInfo {
            symbol: "≡".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );

    // Mathematical ordering
    ops.insert(
        "≺".to_string(),
        OperatorInfo {
            symbol: "≺".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "≻".to_string(),
        OperatorInfo {
            symbol: "≻".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "≼".to_string(),
        OperatorInfo {
            symbol: "≼".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "≽".to_string(),
        OperatorInfo {
            symbol: "≽".to_string(),
            precedence: Precedence(50),
            associativity: Associativity::None,
        },
    );

    // Mathematical operations
    ops.insert(
        "⊕".to_string(),
        OperatorInfo {
            symbol: "⊕".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "⊗".to_string(),
        OperatorInfo {
            symbol: "⊗".to_string(),
            precedence: Precedence(70),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "⊞".to_string(),
        OperatorInfo {
            symbol: "⊞".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "⊠".to_string(),
        OperatorInfo {
            symbol: "⊠".to_string(),
            precedence: Precedence(70),
            associativity: Associativity::Left,
        },
    );

    // Arrows and mappings
    ops.insert(
        "↦".to_string(),
        OperatorInfo {
            symbol: "↦".to_string(),
            precedence: Precedence(25),
            associativity: Associativity::Right,
        },
    );
    ops.insert(
        "⟶".to_string(),
        OperatorInfo {
            symbol: "⟶".to_string(),
            precedence: Precedence(25),
            associativity: Associativity::Right,
        },
    );
    ops.insert(
        "⟵".to_string(),
        OperatorInfo {
            symbol: "⟵".to_string(),
            precedence: Precedence(25),
            associativity: Associativity::Left,
        },
    );

    // Division variants
    ops.insert(
        "÷".to_string(),
        OperatorInfo {
            symbol: "÷".to_string(),
            precedence: Precedence(70),
            associativity: Associativity::Left,
        },
    );

    // Multiplication variants
    ops.insert(
        "×".to_string(),
        OperatorInfo {
            symbol: "×".to_string(),
            precedence: Precedence(70),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "⋅".to_string(),
        OperatorInfo {
            symbol: "⋅".to_string(),
            precedence: Precedence(70),
            associativity: Associativity::Left,
        },
    );

    // Plus/minus variants
    ops.insert(
        "±".to_string(),
        OperatorInfo {
            symbol: "±".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "∓".to_string(),
        OperatorInfo {
            symbol: "∓".to_string(),
            precedence: Precedence(65),
            associativity: Associativity::Left,
        },
    );

    // Pipe operators
    ops.insert(
        "|>".to_string(),
        OperatorInfo {
            symbol: "|>".to_string(),
            precedence: Precedence(10),
            associativity: Associativity::Left,
        },
    );
    ops.insert(
        "<|".to_string(),
        OperatorInfo {
            symbol: "<|".to_string(),
            precedence: Precedence(10),
            associativity: Associativity::Right,
        },
    );

    // Dollar operator (low precedence application)
    ops.insert(
        "$".to_string(),
        OperatorInfo {
            symbol: "$".to_string(),
            precedence: Precedence(10),
            associativity: Associativity::Right,
        },
    );

    // Member access
    ops.insert(
        ".".to_string(),
        OperatorInfo {
            symbol: ".".to_string(),
            precedence: Precedence(100),
            associativity: Associativity::Left,
        },
    );

    ops
});

static UNARY_OPERATORS: Lazy<HashMap<String, OperatorInfo>> = Lazy::new(|| {
    let mut ops = HashMap::new();

    // Negation
    ops.insert(
        "-".to_string(),
        OperatorInfo {
            symbol: "-".to_string(),
            precedence: Precedence(75),
            associativity: Associativity::None,
        },
    );

    // Logical not
    ops.insert(
        "¬".to_string(),
        OperatorInfo {
            symbol: "¬".to_string(),
            precedence: Precedence(40),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "!".to_string(),
        OperatorInfo {
            symbol: "!".to_string(),
            precedence: Precedence(75),
            associativity: Associativity::None,
        },
    );

    // Mathematical unary operators
    ops.insert(
        "√".to_string(),
        OperatorInfo {
            symbol: "√".to_string(),
            precedence: Precedence(85),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "∃".to_string(),
        OperatorInfo {
            symbol: "∃".to_string(),
            precedence: Precedence(30),
            associativity: Associativity::None,
        },
    );
    // Note: ∀ (forall) is NOT a unary operator - it's handled by forall_term()
    // ops.insert(
    //     "∀".to_string(),
    //     OperatorInfo {
    //         symbol: "∀".to_string(),
    //         precedence: Precedence(30),
    //         associativity: Associativity::None,
    //     },
    // );
    ops.insert(
        "∆".to_string(),
        OperatorInfo {
            symbol: "∆".to_string(),
            precedence: Precedence(75),
            associativity: Associativity::None,
        },
    );
    ops.insert(
        "∇".to_string(),
        OperatorInfo {
            symbol: "∇".to_string(),
            precedence: Precedence(75),
            associativity: Associativity::None,
        },
    );

    ops
});

/// Get information about a binary operator
pub fn get_binary_operator(symbol: &str) -> Option<&'static OperatorInfo> {
    BINARY_OPERATORS.get(symbol)
}

/// Get information about a unary operator
pub fn get_unary_operator(symbol: &str) -> Option<&'static OperatorInfo> {
    UNARY_OPERATORS.get(symbol)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_operators() {
        assert!(get_binary_operator("+").is_some());
        assert!(get_binary_operator("*").is_some());
        assert!(get_binary_operator("->").is_some());
        assert!(get_binary_operator("&&").is_some());
    }

    #[test]
    fn test_unary_operators() {
        assert!(get_unary_operator("-").is_some());
        assert!(get_unary_operator("!").is_some());
        assert!(get_unary_operator("¬").is_some());
    }

    #[test]
    fn test_precedence_ordering() {
        assert!(Precedence(10) < Precedence(20));
        assert!(Precedence(50) < Precedence(70));
        assert!(Precedence::MIN < Precedence::MAX);
    }
}
