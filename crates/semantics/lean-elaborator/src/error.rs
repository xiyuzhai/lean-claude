//! Error types for the elaborator

use lean_kernel::Name;
use lean_syn_expr::SyntaxKind;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ElabError {
    #[error("Missing syntax")]
    MissingSyntax,

    #[error("Unsupported syntax kind: {0}")]
    UnsupportedSyntax(SyntaxKind),

    #[error("Invalid syntax: {0}")]
    InvalidSyntax(String),

    #[error("Unknown identifier: {0}")]
    UnknownIdentifier(Name),

    #[error("Type mismatch: expected {expected}, got {got}")]
    TypeMismatch { expected: String, got: String },

    #[error("Cannot infer type")]
    CannotInferType,

    #[error("Metavariable {0} is unassigned")]
    UnassignedMetavar(Name),

    #[error("Invalid projection: {0}")]
    InvalidProjection(String),

    #[error("Universe level error: {0}")]
    UniverseLevelError(String),

    #[error("Elaboration failed: {0}")]
    ElaborationFailed(String),

    #[error("Unsupported feature: {0}")]
    UnsupportedFeature(String),

    #[error("Module not found: {0}")]
    ModuleNotFound(Name),

    #[error("Import cycle detected: {0}")]
    ImportCycle(Name),

    #[error("IO error: {0}")]
    IOError(String),

    #[error("Parse error: {0}")]
    ParseError(String),

    #[error("Namespace error: {0}")]
    NamespaceError(String),
}
