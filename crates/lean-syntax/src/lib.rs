#![feature(let_chains)]

use lean_eterned::BaseCoword;
use smallvec::SmallVec;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourcePos {
    pub line: u32,
    pub column: u32,
    pub offset: usize,
}

impl SourcePos {
    pub fn new(line: u32, column: u32, offset: usize) -> Self {
        Self { line, column, offset }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
    
    // Terms
    App,
    Lambda,
    Forall,
    Let,
    Have,
    Show,
    By,
    
    // Commands
    Command,
    Declaration,
    
    // Tactics
    Tactic,
    TacticSeq,
    
    // Other
    Module,
    Error,
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
            SyntaxKind::App => "application",
            SyntaxKind::Lambda => "lambda",
            SyntaxKind::Forall => "forall",
            SyntaxKind::Let => "let",
            SyntaxKind::Have => "have",
            SyntaxKind::Show => "show",
            SyntaxKind::By => "by",
            SyntaxKind::Command => "command",
            SyntaxKind::Declaration => "declaration",
            SyntaxKind::Tactic => "tactic",
            SyntaxKind::TacticSeq => "tactic sequence",
            SyntaxKind::Module => "module",
            SyntaxKind::Error => "error",
        };
        write!(f, "{}", s)
    }
}