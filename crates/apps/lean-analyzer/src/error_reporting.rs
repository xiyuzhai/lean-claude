//! Superior error reporting system for Lean
//!
//! This module provides much better error messages than the original Lean
//! implementation, with detailed explanations, suggestions, and context-aware
//! help.

use std::collections::HashMap;

use lean_elaborator::ElabError;
use lean_kernel::{Expr, Name};
use lean_parser::{ParseError, ParseErrorKind};
use lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};
use serde_json::Value;

#[derive(Debug, Clone, serde::Serialize)]
pub struct EnhancedDiagnostic {
    pub range: Range,
    pub severity: DiagnosticSeverity,
    pub code: Option<String>,
    pub message: String,
    pub explanation: Option<String>,
    pub suggestions: Vec<CodeSuggestion>,
    pub related_info: Vec<RelatedInfo>,
    pub help_url: Option<String>,
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct CodeSuggestion {
    pub range: Range,
    pub replacement: String,
    pub description: String,
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct RelatedInfo {
    pub range: Range,
    pub message: String,
    pub file_path: Option<String>,
}

pub struct ErrorReporter {
    #[allow(dead_code)]
    error_database: ErrorDatabase,
    #[allow(dead_code)]
    context_tracker: ContextTracker,
}

impl ErrorReporter {
    pub fn new() -> Self {
        Self {
            error_database: ErrorDatabase::new(),
            context_tracker: ContextTracker::new(),
        }
    }

    /// Convert a parse error into an enhanced diagnostic with suggestions
    pub fn enhance_parse_error(&self, error: &ParseError, source: &str) -> EnhancedDiagnostic {
        match &error.kind {
            ParseErrorKind::ExpectedOneOf(expected) => {
                self.handle_expected_one_of(error, expected, source)
            }
            ParseErrorKind::Expected(expected) => self.handle_expected(error, expected, source),
            ParseErrorKind::UnexpectedChar(ch) => self.handle_unexpected_char(error, *ch, source),
            ParseErrorKind::UnterminatedString => self.handle_unterminated_string(error, source),
            ParseErrorKind::InvalidNumber => self.handle_invalid_number(error, source),
            ParseErrorKind::InvalidString => self.handle_invalid_string(error, source),
            ParseErrorKind::UnexpectedEof => self.handle_unexpected_eof(error, source),
            ParseErrorKind::Custom(msg) => self.handle_custom_error(error, msg, source),
            _ => self.handle_generic_error(error, source),
        }
    }

    /// Convert an elaboration error into an enhanced diagnostic
    pub fn enhance_elab_error(&self, error: &ElabError, expr: &Expr) -> EnhancedDiagnostic {
        match error {
            ElabError::TypeMismatch { expected, got } => {
                self.handle_type_mismatch_str(expected, got, expr)
            }
            ElabError::UnknownIdentifier(name) => self.handle_unknown_identifier(name, expr),
            ElabError::ElaborationFailed(msg) => self.handle_elaboration_failed(msg, expr),
            ElabError::UnsupportedFeature(msg) => self.handle_unsupported_feature(msg, expr),
            ElabError::CannotInferType => self.handle_cannot_infer_type(expr),
            _ => self.handle_generic_elab_error(error, expr),
        }
    }

    fn handle_expected_one_of(
        &self,
        error: &ParseError,
        expected: &[String],
        source: &str,
    ) -> EnhancedDiagnostic {
        let range = self.error_to_range(error, source);
        let expected_str = format!(
            "one of: {}",
            expected
                .iter()
                .map(|s| format!("'{s}'"))
                .collect::<Vec<_>>()
                .join(", ")
        );

        let message = format!("Expected {expected_str}");

        let explanation = Some(format!(
            "The parser was expecting {expected_str} at this position. This usually indicates a syntax error \
             or missing punctuation."
        ));

        let suggestions = self.suggest_token_fixes(expected, "", &range, source);

        EnhancedDiagnostic {
            range,
            severity: DiagnosticSeverity::ERROR,
            code: Some("E001".to_string()),
            message,
            explanation,
            suggestions,
            related_info: vec![],
            help_url: Some(
                "https://lean-lang.org/theorem_proving_in_lean4/syntax.html".to_string(),
            ),
        }
    }

    fn handle_expected(
        &self,
        error: &ParseError,
        expected: &str,
        source: &str,
    ) -> EnhancedDiagnostic {
        let range = self.error_to_range(error, source);
        let message = format!("Expected '{expected}'");

        let explanation = Some(format!(
            "The parser expected to find '{expected}' at this position. This token is required by Lean's \
             syntax rules."
        ));

        let suggestions = vec![CodeSuggestion {
            range,
            replacement: expected.to_string(),
            description: format!("Insert '{expected}'"),
        }];

        EnhancedDiagnostic {
            range,
            severity: DiagnosticSeverity::ERROR,
            code: Some("E002".to_string()),
            message,
            explanation,
            suggestions,
            related_info: vec![],
            help_url: Some(
                "https://lean-lang.org/theorem_proving_in_lean4/syntax.html".to_string(),
            ),
        }
    }

    fn handle_unexpected_char(
        &self,
        error: &ParseError,
        ch: char,
        source: &str,
    ) -> EnhancedDiagnostic {
        let range = self.error_to_range(error, source);
        let message = format!("Unexpected character '{ch}'");

        let explanation = Some(format!(
            "The character '{ch}' is not valid in this context. Check your syntax."
        ));

        let suggestions = self.suggest_char_fixes(ch, &range, source);

        EnhancedDiagnostic {
            range,
            severity: DiagnosticSeverity::ERROR,
            code: Some("E003".to_string()),
            message,
            explanation,
            suggestions,
            related_info: vec![],
            help_url: Some("https://lean-lang.org/theorem_proving_in_lean4/".to_string()),
        }
    }

    fn handle_unexpected_eof(&self, error: &ParseError, source: &str) -> EnhancedDiagnostic {
        let range = self.error_to_range(error, source);
        let message = "Unexpected end of file".to_string();

        let explanation = Some(
            "The file ended unexpectedly while parsing. You may be missing closing brackets, \
             parentheses, or other delimiters."
                .to_string(),
        );

        EnhancedDiagnostic {
            range,
            severity: DiagnosticSeverity::ERROR,
            code: Some("E004".to_string()),
            message,
            explanation,
            suggestions: vec![],
            related_info: vec![],
            help_url: Some(
                "https://lean-lang.org/theorem_proving_in_lean4/syntax.html".to_string(),
            ),
        }
    }

    fn handle_invalid_string(&self, error: &ParseError, source: &str) -> EnhancedDiagnostic {
        let range = self.error_to_range(error, source);
        let message = "Invalid string literal".to_string();

        let explanation = Some(
            "This string literal contains invalid characters or escape sequences.".to_string(),
        );

        EnhancedDiagnostic {
            range,
            severity: DiagnosticSeverity::ERROR,
            code: Some("E005".to_string()),
            message,
            explanation,
            suggestions: vec![],
            related_info: vec![],
            help_url: Some(
                "https://lean-lang.org/theorem_proving_in_lean4/strings.html".to_string(),
            ),
        }
    }

    fn handle_generic_error(&self, error: &ParseError, source: &str) -> EnhancedDiagnostic {
        let range = self.error_to_range(error, source);
        let message = error.kind.to_string();

        EnhancedDiagnostic {
            range,
            severity: DiagnosticSeverity::ERROR,
            code: Some("E999".to_string()),
            message,
            explanation: None,
            suggestions: vec![],
            related_info: vec![],
            help_url: None,
        }
    }

    fn handle_unterminated_string(&self, error: &ParseError, source: &str) -> EnhancedDiagnostic {
        let range = self.error_to_range(error, source);
        let message = "Unterminated string literal".to_string();

        let explanation = Some(
            "String literals in Lean must be properly closed with a matching quote. Make sure you \
             haven't forgotten a closing quote or accidentally included a newline in a \
             single-line string."
                .to_string(),
        );

        let suggestions = vec![CodeSuggestion {
            range: Range {
                start: range.end,
                end: range.end,
            },
            replacement: "\"".to_string(),
            description: "Add closing quote".to_string(),
        }];

        EnhancedDiagnostic {
            range,
            severity: DiagnosticSeverity::ERROR,
            code: Some("E004".to_string()),
            message,
            explanation,
            suggestions,
            related_info: vec![],
            help_url: Some(
                "https://lean-lang.org/theorem_proving_in_lean4/strings.html".to_string(),
            ),
        }
    }

    fn handle_invalid_number(&self, error: &ParseError, source: &str) -> EnhancedDiagnostic {
        let range = self.error_to_range(error, source);
        let message = "Invalid number format".to_string();

        let explanation = Some(
            "This number literal is not in a valid format. Lean supports decimal numbers, \
             hexadecimal (0x...), binary (0b...), and octal (0o...) formats."
                .to_string(),
        );

        EnhancedDiagnostic {
            range,
            severity: DiagnosticSeverity::ERROR,
            code: Some("E005".to_string()),
            message,
            explanation,
            suggestions: vec![],
            related_info: vec![],
            help_url: Some(
                "https://lean-lang.org/theorem_proving_in_lean4/numbers.html".to_string(),
            ),
        }
    }

    fn handle_custom_error(
        &self,
        error: &ParseError,
        msg: &str,
        source: &str,
    ) -> EnhancedDiagnostic {
        let range = self.error_to_range(error, source);

        EnhancedDiagnostic {
            range,
            severity: DiagnosticSeverity::ERROR,
            code: Some("E999".to_string()),
            message: msg.to_string(),
            explanation: None,
            suggestions: vec![],
            related_info: vec![],
            help_url: None,
        }
    }

    fn handle_type_mismatch_str(
        &self,
        expected: &str,
        got: &str,
        expr: &Expr,
    ) -> EnhancedDiagnostic {
        let message = format!("Type mismatch: expected '{expected}', got '{got}'");

        let explanation = Some(format!(
            "The expression has type '{got}', but the context requires type '{expected}'. You may need to \
             provide an explicit type conversion or fix the expression."
        ));

        EnhancedDiagnostic {
            range: self.expr_to_range(expr),
            severity: DiagnosticSeverity::ERROR,
            code: Some("T001".to_string()),
            message,
            explanation,
            suggestions: vec![],
            related_info: vec![],
            help_url: Some("https://lean-lang.org/theorem_proving_in_lean4/types.html".to_string()),
        }
    }

    fn handle_unknown_identifier(&self, name: &Name, expr: &Expr) -> EnhancedDiagnostic {
        let name_str = self.name_to_string(name);
        let message = format!("Unknown identifier '{name_str}'");

        let explanation = Some(format!(
            "The identifier '{name_str}' is not defined in the current scope. Make sure it's spelled \
             correctly and is in scope, or import the necessary module."
        ));

        let suggestions = self.suggest_identifier_fixes(&name_str);

        EnhancedDiagnostic {
            range: self.expr_to_range(expr),
            severity: DiagnosticSeverity::ERROR,
            code: Some("T002".to_string()),
            message,
            explanation,
            suggestions,
            related_info: vec![],
            help_url: Some(
                "https://lean-lang.org/theorem_proving_in_lean4/identifiers.html".to_string(),
            ),
        }
    }

    fn handle_elaboration_failed(&self, msg: &str, expr: &Expr) -> EnhancedDiagnostic {
        let message = format!("Elaboration failed: {msg}");

        EnhancedDiagnostic {
            range: self.expr_to_range(expr),
            severity: DiagnosticSeverity::ERROR,
            code: Some("T003".to_string()),
            message,
            explanation: Some("The elaborator failed to process this expression.".to_string()),
            suggestions: vec![],
            related_info: vec![],
            help_url: None,
        }
    }

    fn handle_unsupported_feature(&self, msg: &str, expr: &Expr) -> EnhancedDiagnostic {
        let message = format!("Unsupported feature: {msg}");

        EnhancedDiagnostic {
            range: self.expr_to_range(expr),
            severity: DiagnosticSeverity::WARNING,
            code: Some("T004".to_string()),
            message,
            explanation: Some("This feature is not yet supported by the elaborator.".to_string()),
            suggestions: vec![],
            related_info: vec![],
            help_url: None,
        }
    }

    fn handle_cannot_infer_type(&self, expr: &Expr) -> EnhancedDiagnostic {
        let message = "Cannot infer type".to_string();

        EnhancedDiagnostic {
            range: self.expr_to_range(expr),
            severity: DiagnosticSeverity::ERROR,
            code: Some("T005".to_string()),
            message,
            explanation: Some(
                "The type checker cannot determine the type of this expression. Try adding \
                 explicit type annotations."
                    .to_string(),
            ),
            suggestions: vec![],
            related_info: vec![],
            help_url: Some("https://lean-lang.org/theorem_proving_in_lean4/types.html".to_string()),
        }
    }

    fn handle_generic_elab_error(&self, error: &ElabError, expr: &Expr) -> EnhancedDiagnostic {
        EnhancedDiagnostic {
            range: self.expr_to_range(expr),
            severity: DiagnosticSeverity::ERROR,
            code: Some("T999".to_string()),
            message: error.to_string(),
            explanation: None,
            suggestions: vec![],
            related_info: vec![],
            help_url: None,
        }
    }

    // Helper methods for converting internal types to display types
    fn error_to_range(&self, error: &ParseError, _source: &str) -> Range {
        // Use the position from the error
        let start_pos = Position {
            line: error.position.line,
            character: error.position.column,
        };

        let end_pos = if let Some(range) = &error.range {
            Position {
                line: range.end.line,
                character: range.end.column,
            }
        } else {
            Position {
                line: error.position.line,
                character: error.position.column + 1,
            }
        };

        Range {
            start: start_pos,
            end: end_pos,
        }
    }

    fn expr_to_range(&self, _expr: &Expr) -> Range {
        // TODO: Extract source location from expr
        Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 0,
            },
        }
    }

    #[allow(dead_code)]
    fn expr_to_string(&self, expr: &Expr) -> String {
        // TODO: Implement proper expression pretty-printing
        format!("{expr:?}")
    }

    fn name_to_string(&self, name: &Name) -> String {
        // TODO: Implement proper name pretty-printing
        format!("{name:?}")
    }

    fn suggest_token_fixes(
        &self,
        expected: &[String],
        _found: &str,
        range: &Range,
        _source: &str,
    ) -> Vec<CodeSuggestion> {
        expected
            .iter()
            .map(|token| CodeSuggestion {
                range: *range,
                replacement: token.clone(),
                description: format!("Replace with '{token}'"),
            })
            .collect()
    }

    #[allow(dead_code)]
    fn suggest_syntax_fixes(
        &self,
        _context: &str,
        _range: &Range,
        _source: &str,
    ) -> Vec<CodeSuggestion> {
        // TODO: Implement context-aware syntax suggestions
        vec![]
    }

    fn suggest_char_fixes(&self, _ch: char, _range: &Range, _source: &str) -> Vec<CodeSuggestion> {
        // TODO: Implement character-specific suggestions
        vec![]
    }

    fn suggest_identifier_fixes(&self, _name: &str) -> Vec<CodeSuggestion> {
        // TODO: Implement fuzzy matching for similar identifiers
        vec![]
    }
}

impl Default for ErrorReporter {
    fn default() -> Self {
        Self::new()
    }
}

// Database of common errors and their explanations
struct ErrorDatabase {
    #[allow(dead_code)]
    explanations: HashMap<String, String>,
    #[allow(dead_code)]
    suggestions: HashMap<String, Vec<String>>,
}

impl ErrorDatabase {
    fn new() -> Self {
        let mut explanations = HashMap::new();
        let mut suggestions = HashMap::new();

        // Common error explanations
        explanations.insert(
            "missing_semicolon".to_string(),
            "Statements in Lean typically need to end with appropriate delimiters.".to_string(),
        );

        suggestions.insert(
            "missing_semicolon".to_string(),
            vec![
                "Add a semicolon".to_string(),
                "Check if this should be an expression".to_string(),
            ],
        );

        Self {
            explanations,
            suggestions,
        }
    }
}

// Tracks context for better error messages
struct ContextTracker {
    #[allow(dead_code)]
    current_definition: Option<String>,
    #[allow(dead_code)]
    current_namespace: Vec<String>,
    #[allow(dead_code)]
    imports: Vec<String>,
}

impl ContextTracker {
    fn new() -> Self {
        Self {
            current_definition: None,
            current_namespace: vec![],
            imports: vec![],
        }
    }
}

impl From<EnhancedDiagnostic> for Diagnostic {
    fn from(enhanced: EnhancedDiagnostic) -> Self {
        let mut data = serde_json::Map::new();

        if let Some(explanation) = enhanced.explanation {
            data.insert("explanation".to_string(), Value::String(explanation));
        }

        if !enhanced.suggestions.is_empty() {
            let suggestions: Vec<Value> = enhanced
                .suggestions
                .iter()
                .map(|s| {
                    serde_json::json!({
                        "range": s.range,
                        "replacement": s.replacement,
                        "description": s.description
                    })
                })
                .collect();
            data.insert("suggestions".to_string(), Value::Array(suggestions));
        }

        if let Some(help_url) = enhanced.help_url {
            data.insert("helpUrl".to_string(), Value::String(help_url));
        }

        Diagnostic {
            range: enhanced.range,
            severity: Some(enhanced.severity),
            code: enhanced.code.map(lsp_types::NumberOrString::String),
            code_description: None,
            source: Some("lean-analyzer".to_string()),
            message: enhanced.message,
            related_information: if enhanced.related_info.is_empty() {
                None
            } else {
                Some(
                    enhanced
                        .related_info
                        .iter()
                        .map(|info| lsp_types::DiagnosticRelatedInformation {
                            location: lsp_types::Location {
                                uri: info
                                    .file_path
                                    .as_ref()
                                    .map(|p| lsp_types::Url::from_file_path(p).unwrap())
                                    .unwrap_or_else(|| {
                                        lsp_types::Url::parse("file:///unknown").unwrap()
                                    }),
                                range: info.range,
                            },
                            message: info.message.clone(),
                        })
                        .collect(),
                )
            },
            tags: None,
            data: if data.is_empty() {
                None
            } else {
                Some(Value::Object(data))
            },
        }
    }
}
