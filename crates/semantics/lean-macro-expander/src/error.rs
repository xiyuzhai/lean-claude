use lean_syn_expr::SourceRange;
use thiserror::Error;

pub type ExpansionResult<T> = Result<T, ExpansionError>;

#[derive(Debug, Clone, Error)]
pub enum ExpansionError {
    #[error("Macro not found: {name}")]
    MacroNotFound { name: String, range: SourceRange },

    #[error("Pattern match failed")]
    PatternMatchFailed { range: SourceRange },

    #[error("Invalid macro definition")]
    InvalidMacroDefinition { message: String, range: SourceRange },

    #[error("Expansion limit exceeded")]
    ExpansionLimitExceeded { limit: usize },

    #[error("Invalid syntax quotation")]
    InvalidSyntaxQuotation { message: String, range: SourceRange },

    #[error("Invalid antiquotation")]
    InvalidAntiquotation { message: String, range: SourceRange },

    #[error("Unbound variable: {name}")]
    UnboundVariable {
        name: eterned::BaseCoword,
        range: SourceRange,
    },

    #[error("Invalid macro syntax: {0}")]
    InvalidMacroSyntax(String),

    #[error("Invalid template")]
    InvalidTemplate { message: String, range: SourceRange },
}
