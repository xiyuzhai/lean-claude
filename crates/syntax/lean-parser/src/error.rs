use lean_syn_expr::{SourcePos, SourceRange};
use thiserror::Error;

use crate::diagnostic::{Diagnostic, ParseDiagnostic};

#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("{kind} at {position:?}")]
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub position: SourcePos,
    pub range: Option<SourceRange>,
    /// Additional context for error messages
    pub context: Vec<String>,
    /// Suggestions for fixing the error
    pub suggestions: Vec<String>,
    /// Help text
    pub help: Vec<String>,
    /// Example of correct syntax
    pub examples: Vec<String>,
    /// List of expected tokens/constructs
    pub expected_list: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ParseErrorKind {
    #[error("unexpected end of input")]
    UnexpectedEof,

    #[error("unexpected character '{0}'")]
    UnexpectedChar(char),

    #[error("expected {0}")]
    Expected(String),
    
    #[error("expected one of: {}", .0.join(", "))]
    ExpectedOneOf(Vec<String>),

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
            context: Vec::new(),
            suggestions: Vec::new(),
            help: Vec::new(),
            examples: Vec::new(),
            expected_list: Vec::new(),
        }
    }
    
    /// Create a boxed ParseError for use in ParserResult
    pub fn boxed(kind: ParseErrorKind, position: SourcePos) -> Box<Self> {
        Box::new(Self::new(kind, position))
    }

    pub fn with_range(mut self, range: SourceRange) -> Self {
        self.range = Some(range);
        self
    }

    /// Add context about what was being parsed
    pub fn add_context(&mut self, context: impl Into<String>) {
        self.context.push(context.into());
    }

    /// Add a suggestion for fixing the error
    pub fn add_suggestion(&mut self, suggestion: impl Into<String>) {
        self.suggestions.push(suggestion.into());
    }

    /// Add help text
    pub fn add_help(&mut self, help: impl Into<String>) {
        self.help.push(help.into());
    }

    /// Add an example of correct syntax
    pub fn add_example(&mut self, example: impl Into<String>) {
        self.examples.push(example.into());
    }

    /// Add list of expected tokens
    pub fn add_expected_list(&mut self, expected: Vec<String>) {
        self.expected_list = expected;
    }

    /// Convert to a diagnostic for rich error reporting
    pub fn to_diagnostic(&self) -> Diagnostic {
        let mut diagnostic = Diagnostic::error(self.kind.to_string());

        // Set span
        if let Some(range) = self.range {
            diagnostic = diagnostic.with_span(range);
        } else {
            diagnostic = diagnostic.with_span(SourceRange {
                start: self.position,
                end: self.position,
            });
        }

        // Add context as notes
        for ctx in &self.context {
            diagnostic = diagnostic.with_note(format!("while {ctx}"));
        }

        // Add suggestions
        for suggestion in &self.suggestions {
            diagnostic = diagnostic.with_help(format!("try: {suggestion}"));
        }

        // Add help
        for help in &self.help {
            diagnostic = diagnostic.with_help(help.clone());
        }

        // Add examples
        for example in &self.examples {
            diagnostic = diagnostic.with_help(format!("example: {example}"));
        }

        // Add expected list
        if !self.expected_list.is_empty() {
            diagnostic = diagnostic.with_help(format!(
                "expected one of: {}",
                self.expected_list.join(", ")
            ));
        }

        diagnostic
    }

    /// Create a ParseDiagnostic for enhanced error reporting
    pub fn to_parse_diagnostic(&self) -> ParseDiagnostic {
        ParseDiagnostic {
            diagnostic: self.to_diagnostic(),
            similar_valid: Vec::new(),
            context: self.context.clone(),
        }
    }
}

/// Common error patterns with helpful messages
pub fn enhance_error_message(error: &mut ParseError) {
    match &error.kind {
        ParseErrorKind::Expected(expected) => {
            // Add context-specific help
            match expected.as_str() {
                "term" => {
                    error.add_help("a term can be an identifier, number, string, or expression");
                    error.add_example("x, 42, \"hello\", f x y");
                }
                "tactic" => {
                    error.add_help("a tactic tells Lean how to prove a goal");
                    error.add_example("exact h, apply f, intro x");
                }
                "identifier" => {
                    error.add_help("identifiers start with a letter or underscore");
                    error.add_example("x, _foo, myVar");
                }
                _ => {}
            }
        }
        ParseErrorKind::UnexpectedChar(ch) => {
            match ch {
                ';' => {
                    error.add_help("semicolons separate tactics, not terms");
                    error.add_suggestion("remove the semicolon or wrap in parentheses");
                }
                ',' => {
                    error.add_help("commas are used in lists and function arguments");
                    error.add_suggestion("check if you're missing brackets or parentheses");
                }
                _ => {}
            }
        }
        _ => {}
    }
}