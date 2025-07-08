use lean_syn_expr::{SourcePos, SourceRange};
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("{kind} at {position:?}")]
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub position: SourcePos,
    pub range: Option<SourceRange>,
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ParseErrorKind {
    #[error("unexpected end of input")]
    UnexpectedEof,
    
    #[error("unexpected character '{0}'")]
    UnexpectedChar(char),
    
    #[error("expected {0}")]
    Expected(String),
    
    #[error("invalid number literal")]
    InvalidNumber,
    
    #[error("invalid string literal")]
    InvalidString,
    
    #[error("invalid character literal")]
    InvalidChar,
    
    #[error("unterminated string")]
    UnterminatedString,
    
    #[error("unterminated comment")]
    UnterminatedComment,
    
    #[error("{0}")]
    Custom(String),
}

impl ParseError {
    pub fn new(kind: ParseErrorKind, position: SourcePos) -> Self {
        Self {
            kind,
            position,
            range: None,
        }
    }

    pub fn with_range(mut self, range: SourceRange) -> Self {
        self.range = Some(range);
        self
    }
}