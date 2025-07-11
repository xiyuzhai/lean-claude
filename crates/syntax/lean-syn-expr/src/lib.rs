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

/// Represents trivia (whitespace and comments) attached to syntax nodes
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trivia {
    pub kind: TriviaKind,
    pub range: SourceRange,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TriviaKind {
    Whitespace,
    LineComment,    // -- comment
    BlockComment,   // /- comment -/
    DocComment,     // /-- doc comment -/ or /-! doc comment -/
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxNode {
    pub kind: SyntaxKind,
    pub range: SourceRange,
    pub children: SmallVec<[Syntax; 4]>,
    /// Leading trivia (whitespace and comments before this node)
    pub leading_trivia: Vec<Trivia>,
    /// Trailing trivia (whitespace and comments after this node)
    pub trailing_trivia: Vec<Trivia>,
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
    /// Leading trivia (whitespace and comments before this atom)
    pub leading_trivia: Vec<Trivia>,
    /// Trailing trivia (whitespace and comments after this atom)
    pub trailing_trivia: Vec<Trivia>,
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
    InstanceMethod,
    InstanceMethods,
    Class,
    Structure,
    Inductive,
    Mutual,
    Where,
    Extends,
    With,
    Deriving,
    Abbrev,

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
    StructurePattern,
    TuplePattern,

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
    ElabRules,
    ElabRulesList,

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

    // Advanced expressions
    Subtype,
    AnonymousConstructor,
    ExplicitApp,
    Projection,
    List,
    Do,
    Bind,
    Return,

    // Macros and Notation
    Macro,
    MacroDef,
    MacroRules,
    MacroRule,
    Syntax,
    SyntaxQuotation,
    SyntaxAntiquotation,
    SyntaxSplice,
    Notation,
    NotationDef,
    Precedence,
    Attribute,
    AttributeList,

    // Other
    Module,
    Error,
    StringInterpolation,

    // Custom Syntax
    DeclareSyntaxCat,
    SyntaxExtension,
    SyntaxPattern,
    SyntaxParam,
    CustomSyntax,

    // Universe levels
    Sort,
    Type,
    Prop,
    UniverseSucc,
    UniverseMax,
    UniverseIMax,

    // Scoped notation and attributes
    ScopedNotation,
    LocalNotation,
    AttributeInstance,
    MacroPattern,
    MacroExpansion,
    SyntaxDecl,
    Optional,
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

    /// Get leading trivia for this syntax node
    pub fn leading_trivia(&self) -> &[Trivia] {
        match self {
            Syntax::Missing => &[],
            Syntax::Node(node) => &node.leading_trivia,
            Syntax::Atom(atom) => &atom.leading_trivia,
        }
    }

    /// Get trailing trivia for this syntax node
    pub fn trailing_trivia(&self) -> &[Trivia] {
        match self {
            Syntax::Missing => &[],
            Syntax::Node(node) => &node.trailing_trivia,
            Syntax::Atom(atom) => &atom.trailing_trivia,
        }
    }
}

impl SyntaxNode {
    /// Create a new syntax node with empty trivia
    pub fn new(kind: SyntaxKind, range: SourceRange, children: SmallVec<[Syntax; 4]>) -> Self {
        Self {
            kind,
            range,
            children,
            leading_trivia: Vec::new(),
            trailing_trivia: Vec::new(),
        }
    }

    /// Create a new syntax node with specified trivia
    pub fn with_trivia(
        kind: SyntaxKind,
        range: SourceRange,
        children: SmallVec<[Syntax; 4]>,
        leading_trivia: Vec<Trivia>,
        trailing_trivia: Vec<Trivia>,
    ) -> Self {
        Self {
            kind,
            range,
            children,
            leading_trivia,
            trailing_trivia,
        }
    }
}

impl SyntaxAtom {
    /// Create a new syntax atom with empty trivia
    pub fn new(range: SourceRange, value: BaseCoword) -> Self {
        Self {
            range,
            value,
            leading_trivia: Vec::new(),
            trailing_trivia: Vec::new(),
        }
    }

    /// Create a new syntax atom with specified trivia
    pub fn with_trivia(
        range: SourceRange,
        value: BaseCoword,
        leading_trivia: Vec<Trivia>,
        trailing_trivia: Vec<Trivia>,
    ) -> Self {
        Self {
            range,
            value,
            leading_trivia,
            trailing_trivia,
        }
    }
}

impl Trivia {
    /// Create a new trivia item
    pub fn new(kind: TriviaKind, range: SourceRange, text: String) -> Self {
        Self { kind, range, text }
    }

    /// Check if this trivia is whitespace
    pub fn is_whitespace(&self) -> bool {
        matches!(self.kind, TriviaKind::Whitespace)
    }

    /// Check if this trivia is a comment
    pub fn is_comment(&self) -> bool {
        matches!(
            self.kind,
            TriviaKind::LineComment | TriviaKind::BlockComment | TriviaKind::DocComment
        )
    }

    /// Check if this trivia is a documentation comment
    pub fn is_doc_comment(&self) -> bool {
        matches!(self.kind, TriviaKind::DocComment)
    }
}

#[cfg(test)]
mod tests;

impl fmt::Display for TriviaKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            TriviaKind::Whitespace => "whitespace",
            TriviaKind::LineComment => "line comment",
            TriviaKind::BlockComment => "block comment",
            TriviaKind::DocComment => "doc comment",
        };
        write!(f, "{s}")
    }
}

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
            SyntaxKind::InstanceMethod => "instance_method",
            SyntaxKind::InstanceMethods => "instance_methods",
            SyntaxKind::Class => "class",
            SyntaxKind::Structure => "structure",
            SyntaxKind::Inductive => "inductive",
            SyntaxKind::Mutual => "mutual",
            SyntaxKind::Where => "where",
            SyntaxKind::Extends => "extends",
            SyntaxKind::With => "with",
            SyntaxKind::Deriving => "deriving",
            SyntaxKind::Abbrev => "abbrev",
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
            SyntaxKind::StructurePattern => "structure pattern",
            SyntaxKind::TuplePattern => "tuple pattern",
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
            SyntaxKind::ElabRules => "elab_rules",
            SyntaxKind::ElabRulesList => "elab rules list",
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
            SyntaxKind::Subtype => "subtype",
            SyntaxKind::AnonymousConstructor => "anonymous constructor",
            SyntaxKind::ExplicitApp => "explicit application",
            SyntaxKind::Projection => "projection",
            SyntaxKind::List => "list",
            SyntaxKind::Do => "do",
            SyntaxKind::Bind => "bind",
            SyntaxKind::Return => "return",
            SyntaxKind::Macro => "macro",
            SyntaxKind::MacroDef => "macro definition",
            SyntaxKind::MacroRules => "macro rules",
            SyntaxKind::MacroRule => "macro rule",
            SyntaxKind::Syntax => "syntax",
            SyntaxKind::SyntaxQuotation => "syntax quotation",
            SyntaxKind::SyntaxAntiquotation => "syntax antiquotation",
            SyntaxKind::SyntaxSplice => "syntax splice",
            SyntaxKind::Notation => "notation",
            SyntaxKind::NotationDef => "notation definition",
            SyntaxKind::Precedence => "precedence",
            SyntaxKind::Attribute => "attribute",
            SyntaxKind::AttributeList => "attribute list",
            SyntaxKind::Module => "module",
            SyntaxKind::Error => "error",
            SyntaxKind::StringInterpolation => "string interpolation",
            SyntaxKind::DeclareSyntaxCat => "declare_syntax_cat",
            SyntaxKind::SyntaxExtension => "syntax extension",
            SyntaxKind::SyntaxPattern => "syntax pattern",
            SyntaxKind::SyntaxParam => "syntax parameter",
            SyntaxKind::CustomSyntax => "custom syntax",
            SyntaxKind::Sort => "Sort",
            SyntaxKind::Type => "Type",
            SyntaxKind::Prop => "Prop",
            SyntaxKind::UniverseSucc => "universe successor",
            SyntaxKind::UniverseMax => "universe max",
            SyntaxKind::UniverseIMax => "universe imax",
            SyntaxKind::ScopedNotation => "scoped notation",
            SyntaxKind::LocalNotation => "local notation",
            SyntaxKind::AttributeInstance => "attribute instance",
            SyntaxKind::MacroPattern => "macro pattern",
            SyntaxKind::MacroExpansion => "macro expansion",
            SyntaxKind::SyntaxDecl => "syntax declaration",
            SyntaxKind::Optional => "optional",
        };
        write!(f, "{s}")
    }
}
