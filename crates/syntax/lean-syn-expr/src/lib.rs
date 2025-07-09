use std::fmt;

use eterned::BaseCoword;
use smallvec::SmallVec;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourcePos {
    pub line: u32,
    pub column: u32,
    pub offset: usize,
}

impl SourcePos {
    pub fn new(line: u32, column: u32, offset: usize) -> Self {
        Self {
            line,
            column,
            offset,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceRange {
    pub start: SourcePos,
    pub end: SourcePos,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxNode {
    pub kind: SyntaxKind,
    pub range: SourceRange,
    pub children: SmallVec<[Syntax; 4]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Syntax {
    Missing,
    Node(Box<SyntaxNode>),
    Atom(SyntaxAtom),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxAtom {
    pub range: SourceRange,
    pub value: BaseCoword,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SyntaxKind {
    // Atoms
    Identifier,
    NumLit,
    StringLit,
    CharLit,
    Whitespace,
    Comment,

    // Delimiters
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,

    // Operators
    Arrow,  // →
    DArrow, // =>
    Colon,
    ColonEq, // :=
    Dot,
    DotDot, // ..
    Comma,
    Semicolon,
    At,          // @
    Hash,        // #
    Dollar,      // $
    Backtick,    // `
    Question,    // ?
    Exclamation, // !

    // Keywords
    Def,
    Theorem,
    Axiom,
    Constant,
    Variable,
    Universe,
    Namespace,
    End,
    Section,
    Import,
    Open,
    Instance,
    Class,
    Structure,
    Inductive,
    Where,
    Extends,
    With,
    Deriving,

    // Terms
    App,
    Lambda,
    Forall,
    Let,
    BinOp,
    UnaryOp,
    Have,
    Show,
    By,
    Match,
    MatchArm,

    // Patterns
    ConstructorPattern,
    WildcardPattern,

    // Commands
    Command,
    Declaration,
    Field,
    Constructor,
    HashCommand,
    HashCheck,
    HashEval,
    HashPrint,
    HashReduce,

    // Elaboration
    Elab,

    // Tactics
    Tactic,
    TacticSeq,
    TacticAlt,
    Exact,
    Apply,
    Intro,
    Intros,
    Cases,
    Induction,
    Simp,
    SimpExclude,
    Rewrite,
    Rfl,
    Sorry,
    Assumption,
    Contradiction,
    Calc,
    CalcStep,
    TacticHave,
    TacticLet,
    TacticShow,
    Repeat,
    Try,
    First,
    AllGoals,
    Focus,
    CustomTactic,
    CasePattern,

    // Macros and Notation
    Macro,
    MacroDef,
    MacroRules,
    MacroRule,
    Syntax,
    SyntaxQuotation,
    SyntaxAntiquotation,
    Notation,
    NotationDef,
    Precedence,
    Attribute,
    AttributeList,

    // Other
    Module,
    Error,
    StringInterpolation,
}

impl Syntax {
    pub fn is_missing(&self) -> bool {
        matches!(self, Syntax::Missing)
    }

    pub fn range(&self) -> Option<&SourceRange> {
        match self {
            Syntax::Missing => None,
            Syntax::Node(node) => Some(&node.range),
            Syntax::Atom(atom) => Some(&atom.range),
        }
    }

    pub fn kind(&self) -> Option<SyntaxKind> {
        match self {
            Syntax::Missing => None,
            Syntax::Node(node) => Some(node.kind),
            Syntax::Atom(_) => None,
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            Syntax::Atom(atom) => atom.value.as_str(),
            _ => "",
        }
    }
}

#[cfg(test)]
mod tests;

impl fmt::Display for SyntaxKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            SyntaxKind::Identifier => "identifier",
            SyntaxKind::NumLit => "number",
            SyntaxKind::StringLit => "string",
            SyntaxKind::CharLit => "char",
            SyntaxKind::Whitespace => "whitespace",
            SyntaxKind::Comment => "comment",
            SyntaxKind::LeftParen => "(",
            SyntaxKind::RightParen => ")",
            SyntaxKind::LeftBracket => "[",
            SyntaxKind::RightBracket => "]",
            SyntaxKind::LeftBrace => "{",
            SyntaxKind::RightBrace => "}",
            SyntaxKind::Arrow => "→",
            SyntaxKind::DArrow => "=>",
            SyntaxKind::Colon => ":",
            SyntaxKind::ColonEq => ":=",
            SyntaxKind::Dot => ".",
            SyntaxKind::DotDot => "..",
            SyntaxKind::Comma => ",",
            SyntaxKind::Semicolon => ";",
            SyntaxKind::At => "@",
            SyntaxKind::Hash => "#",
            SyntaxKind::Dollar => "$",
            SyntaxKind::Backtick => "`",
            SyntaxKind::Question => "?",
            SyntaxKind::Exclamation => "!",
            SyntaxKind::Def => "def",
            SyntaxKind::Theorem => "theorem",
            SyntaxKind::Axiom => "axiom",
            SyntaxKind::Constant => "constant",
            SyntaxKind::Variable => "variable",
            SyntaxKind::Universe => "universe",
            SyntaxKind::Namespace => "namespace",
            SyntaxKind::End => "end",
            SyntaxKind::Section => "section",
            SyntaxKind::Import => "import",
            SyntaxKind::Open => "open",
            SyntaxKind::Instance => "instance",
            SyntaxKind::Class => "class",
            SyntaxKind::Structure => "structure",
            SyntaxKind::Inductive => "inductive",
            SyntaxKind::Where => "where",
            SyntaxKind::Extends => "extends",
            SyntaxKind::With => "with",
            SyntaxKind::Deriving => "deriving",
            SyntaxKind::App => "application",
            SyntaxKind::Lambda => "lambda",
            SyntaxKind::BinOp => "binary operation",
            SyntaxKind::UnaryOp => "unary operation",
            SyntaxKind::Forall => "forall",
            SyntaxKind::Let => "let",
            SyntaxKind::Have => "have",
            SyntaxKind::Show => "show",
            SyntaxKind::By => "by",
            SyntaxKind::Match => "match",
            SyntaxKind::MatchArm => "match arm",
            SyntaxKind::ConstructorPattern => "constructor pattern",
            SyntaxKind::WildcardPattern => "wildcard pattern",
            SyntaxKind::Command => "command",
            SyntaxKind::Declaration => "declaration",
            SyntaxKind::Field => "field",
            SyntaxKind::Constructor => "constructor",
            SyntaxKind::HashCommand => "hash command",
            SyntaxKind::HashCheck => "#check",
            SyntaxKind::HashEval => "#eval",
            SyntaxKind::HashPrint => "#print",
            SyntaxKind::HashReduce => "#reduce",
            SyntaxKind::Elab => "elab",
            SyntaxKind::Tactic => "tactic",
            SyntaxKind::TacticSeq => "tactic sequence",
            SyntaxKind::TacticAlt => "tactic alternative",
            SyntaxKind::Exact => "exact",
            SyntaxKind::Apply => "apply",
            SyntaxKind::Intro => "intro",
            SyntaxKind::Intros => "intros",
            SyntaxKind::Cases => "cases",
            SyntaxKind::Induction => "induction",
            SyntaxKind::Simp => "simp",
            SyntaxKind::SimpExclude => "simp exclude",
            SyntaxKind::Rewrite => "rewrite",
            SyntaxKind::Rfl => "rfl",
            SyntaxKind::Sorry => "sorry",
            SyntaxKind::Assumption => "assumption",
            SyntaxKind::Contradiction => "contradiction",
            SyntaxKind::Calc => "calc",
            SyntaxKind::CalcStep => "calc step",
            SyntaxKind::TacticHave => "tactic have",
            SyntaxKind::TacticLet => "tactic let",
            SyntaxKind::TacticShow => "tactic show",
            SyntaxKind::Repeat => "repeat",
            SyntaxKind::Try => "try",
            SyntaxKind::First => "first",
            SyntaxKind::AllGoals => "all_goals",
            SyntaxKind::Focus => "focus",
            SyntaxKind::CustomTactic => "custom tactic",
            SyntaxKind::CasePattern => "case pattern",
            SyntaxKind::Macro => "macro",
            SyntaxKind::MacroDef => "macro definition",
            SyntaxKind::MacroRules => "macro rules",
            SyntaxKind::MacroRule => "macro rule",
            SyntaxKind::Syntax => "syntax",
            SyntaxKind::SyntaxQuotation => "syntax quotation",
            SyntaxKind::SyntaxAntiquotation => "syntax antiquotation",
            SyntaxKind::Notation => "notation",
            SyntaxKind::NotationDef => "notation definition",
            SyntaxKind::Precedence => "precedence",
            SyntaxKind::Attribute => "attribute",
            SyntaxKind::AttributeList => "attribute list",
            SyntaxKind::Module => "module",
            SyntaxKind::Error => "error",
            SyntaxKind::StringInterpolation => "string interpolation",
        };
        write!(f, "{s}")
    }
}
