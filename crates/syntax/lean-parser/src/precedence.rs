use std::collections::HashMap;

use once_cell::sync::Lazy;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Precedence(pub u32);

impl Precedence {
    pub const MIN: Precedence = Precedence(0);
    pub const MAX: Precedence = Precedence(1024);
    pub const DEFAULT: Precedence = Precedence(0);

    // Standard precedences following Lean4
    pub const ARROW: Precedence = Precedence(25);
    pub const OR: Precedence = Precedence(30);
    pub const AND: Precedence = Precedence(35);
    pub const CMP: Precedence = Precedence(50); // ==, <, >, ≤, ≥
    pub const ADD: Precedence = Precedence(65); // +, -
    pub const MUL: Precedence = Precedence(70); // *, /
    pub const POW: Precedence = Precedence(80); // ^
    pub const COMPOSE: Precedence = Precedence(90); // ∘
    pub const APP: Precedence = Precedence(1024); // function application

    /// Get the next higher precedence
    pub fn next(self) -> Precedence {
        Precedence(self.0.saturating_add(1))
    }

    /// Get the associativity for standard operators at this precedence
    pub fn associativity(self) -> Associativity {
        // Most operators are left-associative by default
        // Right-associative operators will override this
        match self.0 {
            25 => Associativity::Right, // Function arrow
            _ => Associativity::Left,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
    None,
}

#[derive(Debug, Clone)]
pub struct OperatorInfo {
    pub symbol: String,
    pub precedence: Precedence,
    pub associativity: Associativity,
}

impl OperatorInfo {
    pub fn new(
        symbol: impl Into<String>,
        precedence: Precedence,
        associativity: Associativity,
    ) -> Self {
        Self {
            symbol: symbol.into(),
            precedence,
            associativity,
        }
    }
}

pub static BINARY_OPERATORS: Lazy<HashMap<&'static str, OperatorInfo>> = Lazy::new(|| {
    let mut ops = HashMap::new();

    // Arrow
    ops.insert(
        "->",
        OperatorInfo::new("->", Precedence::ARROW, Associativity::Right),
    );
    ops.insert(
        "→",
        OperatorInfo::new("→", Precedence::ARROW, Associativity::Right),
    );

    // Logical
    ops.insert(
        "||",
        OperatorInfo::new("||", Precedence::OR, Associativity::Right),
    );
    ops.insert(
        "∨",
        OperatorInfo::new("∨", Precedence::OR, Associativity::Right),
    );
    ops.insert(
        "&&",
        OperatorInfo::new("&&", Precedence::AND, Associativity::Right),
    );
    ops.insert(
        "∧",
        OperatorInfo::new("∧", Precedence::AND, Associativity::Right),
    );

    // Comparison
    ops.insert(
        "==",
        OperatorInfo::new("==", Precedence::CMP, Associativity::None),
    );
    ops.insert(
        "=",
        OperatorInfo::new("=", Precedence::CMP, Associativity::None),
    );
    ops.insert(
        "!=",
        OperatorInfo::new("!=", Precedence::CMP, Associativity::None),
    );
    ops.insert(
        "≠",
        OperatorInfo::new("≠", Precedence::CMP, Associativity::None),
    );
    ops.insert(
        "<",
        OperatorInfo::new("<", Precedence::CMP, Associativity::None),
    );
    ops.insert(
        ">",
        OperatorInfo::new(">", Precedence::CMP, Associativity::None),
    );
    ops.insert(
        "<=",
        OperatorInfo::new("<=", Precedence::CMP, Associativity::None),
    );
    ops.insert(
        "≤",
        OperatorInfo::new("≤", Precedence::CMP, Associativity::None),
    );
    ops.insert(
        ">=",
        OperatorInfo::new(">=", Precedence::CMP, Associativity::None),
    );
    ops.insert(
        "≥",
        OperatorInfo::new("≥", Precedence::CMP, Associativity::None),
    );

    // Arithmetic
    ops.insert(
        "+",
        OperatorInfo::new("+", Precedence::ADD, Associativity::Left),
    );
    ops.insert(
        "-",
        OperatorInfo::new("-", Precedence::ADD, Associativity::Left),
    );
    ops.insert(
        "*",
        OperatorInfo::new("*", Precedence::MUL, Associativity::Left),
    );
    ops.insert(
        "/",
        OperatorInfo::new("/", Precedence::MUL, Associativity::Left),
    );
    ops.insert(
        "^",
        OperatorInfo::new("^", Precedence::POW, Associativity::Right),
    );

    // Function composition
    ops.insert(
        "∘",
        OperatorInfo::new("∘", Precedence::COMPOSE, Associativity::Right),
    );
    ops.insert(
        ">>",
        OperatorInfo::new(">>", Precedence::COMPOSE, Associativity::Left),
    );
    ops.insert(
        "<<",
        OperatorInfo::new("<<", Precedence::COMPOSE, Associativity::Right),
    );

    // List operations
    ops.insert(
        "::",
        OperatorInfo::new("::", Precedence(67), Associativity::Right),
    );
    ops.insert(
        "++",
        OperatorInfo::new("++", Precedence(65), Associativity::Right),
    );

    ops
});

pub static UNARY_OPERATORS: Lazy<HashMap<&'static str, OperatorInfo>> = Lazy::new(|| {
    let mut ops = HashMap::new();

    ops.insert(
        "!",
        OperatorInfo::new("!", Precedence(100), Associativity::None),
    );
    ops.insert(
        "¬",
        OperatorInfo::new("¬", Precedence(100), Associativity::None),
    );
    ops.insert(
        "-",
        OperatorInfo::new("-", Precedence(100), Associativity::None),
    );

    ops
});

/// Check if a string is a known binary operator
pub fn is_binary_operator(s: &str) -> bool {
    BINARY_OPERATORS.contains_key(s)
}

/// Check if a string is a known unary operator
pub fn is_unary_operator(s: &str) -> bool {
    UNARY_OPERATORS.contains_key(s)
}

/// Get binary operator info
pub fn get_binary_operator(s: &str) -> Option<&'static OperatorInfo> {
    BINARY_OPERATORS.get(s)
}

/// Get unary operator info
pub fn get_unary_operator(s: &str) -> Option<&'static OperatorInfo> {
    UNARY_OPERATORS.get(s)
}
