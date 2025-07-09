//! Diagnostic system inspired by rustc's excellent error reporting

use lean_syn_expr::{SourcePos, SourceRange};

/// Diagnostic severity levels
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    /// Errors that prevent compilation
    Error,
    /// Warnings about potential issues
    Warning,
    /// Informational notes
    Note,
    /// Help suggestions
    Help,
}

/// A diagnostic message with rich formatting
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// Severity of the diagnostic
    pub severity: Severity,
    /// Primary message
    pub message: String,
    /// Error code (e.g., "E0001")
    pub code: Option<String>,
    /// Primary span where the error occurred
    pub primary_span: Option<SourceRange>,
    /// Additional spans with labels
    pub labeled_spans: Vec<LabeledSpan>,
    /// Subdiagnostics (notes, helps, suggestions)
    pub subdiagnostics: Vec<SubDiagnostic>,
}

/// A span with an associated label
#[derive(Debug, Clone)]
pub struct LabeledSpan {
    pub span: SourceRange,
    pub label: String,
    pub is_primary: bool,
}

/// Additional diagnostic information
#[derive(Debug, Clone)]
pub struct SubDiagnostic {
    pub severity: Severity,
    pub message: String,
    pub span: Option<SourceRange>,
}

impl Diagnostic {
    /// Create a new error diagnostic
    pub fn error(message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            message: message.into(),
            code: None,
            primary_span: None,
            labeled_spans: Vec::new(),
            subdiagnostics: Vec::new(),
        }
    }

    /// Create a new warning diagnostic
    pub fn warning(message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Warning,
            message: message.into(),
            code: None,
            primary_span: None,
            labeled_spans: Vec::new(),
            subdiagnostics: Vec::new(),
        }
    }

    /// Set the error code
    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    /// Set the primary span
    pub fn with_span(mut self, span: SourceRange) -> Self {
        self.primary_span = Some(span);
        self
    }

    /// Add a labeled span
    pub fn with_label(mut self, span: SourceRange, label: impl Into<String>) -> Self {
        self.labeled_spans.push(LabeledSpan {
            span,
            label: label.into(),
            is_primary: false,
        });
        self
    }

    /// Add a note
    pub fn with_note(mut self, message: impl Into<String>) -> Self {
        self.subdiagnostics.push(SubDiagnostic {
            severity: Severity::Note,
            message: message.into(),
            span: None,
        });
        self
    }

    /// Add a help message
    pub fn with_help(mut self, message: impl Into<String>) -> Self {
        self.subdiagnostics.push(SubDiagnostic {
            severity: Severity::Help,
            message: message.into(),
            span: None,
        });
        self
    }

    /// Add a suggestion with a span
    pub fn with_suggestion(
        mut self,
        span: SourceRange,
        message: impl Into<String>,
        suggestion: impl Into<String>,
    ) -> Self {
        self.subdiagnostics.push(SubDiagnostic {
            severity: Severity::Help,
            message: format!("{}: {}", message.into(), suggestion.into()),
            span: Some(span),
        });
        self
    }
}

/// Enhanced parse error with rich diagnostics
#[derive(Debug, Clone)]
pub struct ParseDiagnostic {
    /// The main diagnostic
    pub diagnostic: Diagnostic,
    /// Similar valid constructs (for "did you mean?" suggestions)
    pub similar_valid: Vec<String>,
    /// Context stack (e.g., "while parsing term", "in function body")
    pub context: Vec<String>,
}

impl ParseDiagnostic {
    /// Create from a simple error message
    pub fn error(message: impl Into<String>, pos: SourcePos) -> Self {
        Self {
            diagnostic: Diagnostic::error(message).with_span(SourceRange {
                start: pos,
                end: pos,
            }),
            similar_valid: Vec::new(),
            context: Vec::new(),
        }
    }

    /// Add context about what we were parsing
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context.push(context.into());
        self
    }

    /// Add a similar valid construct
    pub fn with_similar(mut self, similar: impl Into<String>) -> Self {
        self.similar_valid.push(similar.into());
        self
    }

    /// Convert to a user-friendly error message
    pub fn emit(&self, source: &str) -> String {
        DiagnosticEmitter::new(source).emit(&self.diagnostic)
    }
}

/// Emits diagnostics with source code context
pub struct DiagnosticEmitter<'a> {
    lines: Vec<&'a str>,
}

impl<'a> DiagnosticEmitter<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            lines: source.lines().collect(),
        }
    }

    /// Emit a diagnostic with rustc-style formatting
    pub fn emit(&self, diagnostic: &Diagnostic) -> String {
        let mut output = String::new();
        
        // Header with severity and message
        let severity_str = match diagnostic.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
            Severity::Help => "help",
        };
        
        if let Some(code) = &diagnostic.code {
            output.push_str(&format!("{severity_str}[{code}]: {}\n", diagnostic.message));
        } else {
            output.push_str(&format!("{severity_str}: {}\n", diagnostic.message));
        }
        
        // Primary span with source context
        if let Some(span) = &diagnostic.primary_span {
            self.emit_span(&mut output, span, Some(&diagnostic.message));
        }
        
        // Additional labeled spans
        for labeled in &diagnostic.labeled_spans {
            self.emit_span(&mut output, &labeled.span, Some(&labeled.label));
        }
        
        // Subdiagnostics
        for sub in &diagnostic.subdiagnostics {
            let prefix = match sub.severity {
                Severity::Note => "note",
                Severity::Help => "help",
                _ => "note",
            };
            output.push_str(&format!("{prefix}: {}\n", sub.message));
            
            if let Some(span) = &sub.span {
                self.emit_span(&mut output, span, None);
            }
        }
        
        output
    }

    fn emit_span(&self, output: &mut String, span: &SourceRange, label: Option<&str>) {
        let line_num = span.start.line;
        let col = span.start.column;
        
        // Line number and file info
        output.push_str(&format!("  --> {}:{}:{}\n", "<input>", line_num, col));
        
        // Context lines
        if line_num > 0 && (line_num as usize) <= self.lines.len() {
            let line_idx = (line_num - 1) as usize;
            let line = self.lines[line_idx];
            
            // Line number gutter
            let line_num_str = line_num.to_string();
            let gutter_width = line_num_str.len() + 1;
            
            output.push_str(&format!("{:>width$} |\n", "", width = gutter_width));
            output.push_str(&format!("{line_num_str} | {line}\n"));
            
            // Underline
            let underline_start = (col - 1) as usize;
            let underline_end = if span.end.line == span.start.line {
                (span.end.column - 1) as usize
            } else {
                line.len()
            };
            
            output.push_str(&format!("{:>width$} | ", "", width = gutter_width));
            output.push_str(&" ".repeat(underline_start));
            output.push_str(&"^".repeat((underline_end - underline_start).max(1)));
            
            if let Some(label) = label {
                output.push_str(&format!(" {label}"));
            }
            output.push('\n');
        }
    }
}

/// Error recovery suggestions
#[derive(Debug, Clone)]
pub struct RecoverySuggestion {
    /// What to look for
    pub pattern: String,
    /// What to suggest
    pub suggestion: String,
    /// Example of correct usage
    pub example: Option<String>,
}

impl RecoverySuggestion {
    pub fn new(pattern: impl Into<String>, suggestion: impl Into<String>) -> Self {
        Self {
            pattern: pattern.into(),
            suggestion: suggestion.into(),
            example: None,
        }
    }

    pub fn with_example(mut self, example: impl Into<String>) -> Self {
        self.example = Some(example.into());
        self
    }
}