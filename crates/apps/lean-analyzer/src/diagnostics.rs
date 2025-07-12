//! Diagnostic collection and management

use std::{collections::HashMap, path::{Path, PathBuf}, sync::Arc};

use lean_elaborator::ElabError;
use lean_parser::ParseError;
use lsp_types::{Diagnostic, DiagnosticSeverity, Range};
use parking_lot::RwLock;

use crate::error_reporting::{EnhancedDiagnostic, ErrorReporter};

/// Manages diagnostics for all files in the workspace
pub struct DiagnosticsManager {
    /// File path to diagnostics mapping
    file_diagnostics: RwLock<HashMap<PathBuf, Vec<EnhancedDiagnostic>>>,
    /// Error reporter for enhanced diagnostics
    error_reporter: Arc<ErrorReporter>,
}

/// Diagnostic collection for a single file
#[derive(Debug, Clone)]
pub struct FileDiagnostics {
    pub file_path: PathBuf,
    pub version: Option<i32>,
    pub diagnostics: Vec<EnhancedDiagnostic>,
}

/// Severity levels for diagnostics
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DiagnosticLevel {
    Error,
    Warning,
    Information,
    Hint,
}

impl DiagnosticsManager {
    /// Create a new diagnostics manager
    pub fn new() -> Self {
        Self {
            file_diagnostics: RwLock::new(HashMap::new()),
            error_reporter: Arc::new(ErrorReporter::new()),
        }
    }

    /// Update diagnostics for a file from parse errors
    pub fn update_parse_diagnostics(
        &self,
        file_path: &Path,
        parse_errors: &[ParseError],
        source: &str,
    ) {
        let mut diagnostics = Vec::new();

        for error in parse_errors {
            let enhanced = self.error_reporter.enhance_parse_error(error, source);
            diagnostics.push(enhanced);
        }

        self.file_diagnostics
            .write()
            .insert(file_path.to_path_buf(), diagnostics);
    }

    /// Update diagnostics for a file from elaboration errors
    pub fn update_elab_diagnostics(
        &self,
        file_path: &Path,
        elab_errors: &[ElabError],
        expr: &lean_kernel::Expr,
    ) {
        let mut existing_diagnostics = self
            .file_diagnostics
            .read()
            .get(file_path)
            .cloned()
            .unwrap_or_default();

        for error in elab_errors {
            let enhanced = self.error_reporter.enhance_elab_error(error, expr);
            existing_diagnostics.push(enhanced);
        }

        self.file_diagnostics
            .write()
            .insert(file_path.to_path_buf(), existing_diagnostics);
    }

    /// Get diagnostics for a specific file
    pub fn get_file_diagnostics(&self, file_path: &PathBuf) -> Vec<EnhancedDiagnostic> {
        self.file_diagnostics
            .read()
            .get(file_path)
            .cloned()
            .unwrap_or_default()
    }

    /// Get all diagnostics as LSP diagnostics
    pub fn get_lsp_diagnostics(&self, file_path: &PathBuf) -> Vec<Diagnostic> {
        self.get_file_diagnostics(file_path)
            .into_iter()
            .map(|enhanced| enhanced.into())
            .collect()
    }

    /// Clear diagnostics for a file
    pub fn clear_file_diagnostics(&self, file_path: &PathBuf) {
        self.file_diagnostics.write().remove(file_path);
    }

    /// Clear all diagnostics
    pub fn clear_all(&self) {
        self.file_diagnostics.write().clear();
    }

    /// Get diagnostic counts by severity
    pub fn get_diagnostic_counts(&self, file_path: &PathBuf) -> DiagnosticCounts {
        let diagnostics = self.get_file_diagnostics(file_path);

        let mut counts = DiagnosticCounts::default();

        for diagnostic in diagnostics {
            match diagnostic.severity {
                DiagnosticSeverity::ERROR => counts.errors += 1,
                DiagnosticSeverity::WARNING => counts.warnings += 1,
                DiagnosticSeverity::INFORMATION => counts.information += 1,
                DiagnosticSeverity::HINT => counts.hints += 1,
                _ => {}
            }
        }

        counts
    }

    /// Get all files with diagnostics
    pub fn files_with_diagnostics(&self) -> Vec<PathBuf> {
        self.file_diagnostics.read().keys().cloned().collect()
    }

    /// Get workspace-wide diagnostic counts
    pub fn get_workspace_counts(&self) -> DiagnosticCounts {
        let diagnostics = self.file_diagnostics.read();
        let mut total_counts = DiagnosticCounts::default();

        for file_diagnostics in diagnostics.values() {
            for diagnostic in file_diagnostics {
                match diagnostic.severity {
                    DiagnosticSeverity::ERROR => total_counts.errors += 1,
                    DiagnosticSeverity::WARNING => total_counts.warnings += 1,
                    DiagnosticSeverity::INFORMATION => total_counts.information += 1,
                    DiagnosticSeverity::HINT => total_counts.hints += 1,
                    _ => {}
                }
            }
        }

        total_counts
    }

    /// Filter diagnostics by severity
    pub fn filter_by_severity(
        &self,
        file_path: &PathBuf,
        min_severity: DiagnosticSeverity,
    ) -> Vec<EnhancedDiagnostic> {
        self.get_file_diagnostics(file_path)
            .into_iter()
            .filter(|diag| {
                Self::severity_level(diag.severity) <= Self::severity_level(min_severity)
            })
            .collect()
    }

    /// Add a custom diagnostic
    pub fn add_custom_diagnostic(
        &self,
        file_path: &Path,
        range: Range,
        severity: DiagnosticSeverity,
        message: String,
        code: Option<String>,
    ) {
        let diagnostic = EnhancedDiagnostic {
            range,
            severity,
            code,
            message,
            explanation: None,
            suggestions: vec![],
            related_info: vec![],
            help_url: None,
        };

        let mut diagnostics = self.file_diagnostics.write();
        diagnostics
            .entry(file_path.to_path_buf())
            .or_default()
            .push(diagnostic);
    }

    /// Convert diagnostic severity to level for comparison
    fn severity_level(severity: DiagnosticSeverity) -> u8 {
        match severity {
            DiagnosticSeverity::ERROR => 0,
            DiagnosticSeverity::WARNING => 1,
            DiagnosticSeverity::INFORMATION => 2,
            DiagnosticSeverity::HINT => 3,
            _ => 4,
        }
    }

    /// Get diagnostics in a specific range
    pub fn get_diagnostics_in_range(
        &self,
        file_path: &PathBuf,
        range: Range,
    ) -> Vec<EnhancedDiagnostic> {
        self.get_file_diagnostics(file_path)
            .into_iter()
            .filter(|diag| Self::ranges_overlap(diag.range, range))
            .collect()
    }

    /// Check if two ranges overlap
    fn ranges_overlap(range1: Range, range2: Range) -> bool {
        !(range1.end < range2.start || range2.end < range1.start)
    }

    /// Export diagnostics to a format suitable for external tools
    pub fn export_diagnostics(&self, format: DiagnosticExportFormat) -> String {
        match format {
            DiagnosticExportFormat::Json => self.export_as_json(),
            DiagnosticExportFormat::Sarif => self.export_as_sarif(),
            DiagnosticExportFormat::Text => self.export_as_text(),
        }
    }

    /// Export diagnostics as JSON
    fn export_as_json(&self) -> String {
        let diagnostics = self.file_diagnostics.read();
        serde_json::to_string_pretty(&*diagnostics).unwrap_or_default()
    }

    /// Export diagnostics as SARIF format
    fn export_as_sarif(&self) -> String {
        // TODO: Implement SARIF export
        "SARIF export not yet implemented".to_string()
    }

    /// Export diagnostics as plain text
    fn export_as_text(&self) -> String {
        let diagnostics = self.file_diagnostics.read();
        let mut output = String::new();

        for (file_path, file_diagnostics) in diagnostics.iter() {
            if !file_diagnostics.is_empty() {
                output.push_str(&format!("\nFile: {}\n", file_path.display()));
                output.push_str(&"-".repeat(50));
                output.push('\n');

                for diagnostic in file_diagnostics {
                    let severity_str = match diagnostic.severity {
                        DiagnosticSeverity::ERROR => "ERROR",
                        DiagnosticSeverity::WARNING => "WARNING",
                        DiagnosticSeverity::INFORMATION => "INFO",
                        DiagnosticSeverity::HINT => "HINT",
                        _ => "UNKNOWN",
                    };

                    output.push_str(&format!(
                        "{}:{}:{}: {}: {}\n",
                        file_path.display(),
                        diagnostic.range.start.line + 1,
                        diagnostic.range.start.character + 1,
                        severity_str,
                        diagnostic.message
                    ));

                    if let Some(explanation) = &diagnostic.explanation {
                        output.push_str(&format!("  Explanation: {explanation}\n"));
                    }

                    if !diagnostic.suggestions.is_empty() {
                        output.push_str("  Suggestions:\n");
                        for suggestion in &diagnostic.suggestions {
                            output.push_str(&format!("    - {}\n", suggestion.description));
                        }
                    }

                    output.push('\n');
                }
            }
        }

        output
    }
}

/// Diagnostic counts by severity
#[derive(Debug, Clone, Default)]
pub struct DiagnosticCounts {
    pub errors: usize,
    pub warnings: usize,
    pub information: usize,
    pub hints: usize,
}

impl DiagnosticCounts {
    /// Get the total number of diagnostics
    pub fn total(&self) -> usize {
        self.errors + self.warnings + self.information + self.hints
    }

    /// Check if there are any errors
    pub fn has_errors(&self) -> bool {
        self.errors > 0
    }

    /// Check if there are any warnings or errors
    pub fn has_warnings_or_errors(&self) -> bool {
        self.errors > 0 || self.warnings > 0
    }
}

/// Export formats for diagnostics
#[derive(Debug, Clone, Copy)]
pub enum DiagnosticExportFormat {
    Json,
    Sarif,
    Text,
}

impl Default for DiagnosticsManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use lsp_types::Position;

    use super::*;

    #[test]
    fn test_diagnostic_counts() {
        let manager = DiagnosticsManager::new();
        let file_path = PathBuf::from("test.lean");

        // Add some diagnostics
        manager.add_custom_diagnostic(
            &file_path,
            Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 0,
                    character: 10,
                },
            },
            DiagnosticSeverity::ERROR,
            "Test error".to_string(),
            Some("E001".to_string()),
        );

        manager.add_custom_diagnostic(
            &file_path,
            Range {
                start: Position {
                    line: 1,
                    character: 0,
                },
                end: Position {
                    line: 1,
                    character: 10,
                },
            },
            DiagnosticSeverity::WARNING,
            "Test warning".to_string(),
            Some("W001".to_string()),
        );

        let counts = manager.get_diagnostic_counts(&file_path);
        assert_eq!(counts.errors, 1);
        assert_eq!(counts.warnings, 1);
        assert_eq!(counts.total(), 2);
        assert!(counts.has_errors());
        assert!(counts.has_warnings_or_errors());
    }

    #[test]
    fn test_range_overlap() {
        let range1 = Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 10,
            },
        };

        let range2 = Range {
            start: Position {
                line: 0,
                character: 5,
            },
            end: Position {
                line: 0,
                character: 15,
            },
        };

        let range3 = Range {
            start: Position {
                line: 1,
                character: 0,
            },
            end: Position {
                line: 1,
                character: 10,
            },
        };

        assert!(DiagnosticsManager::ranges_overlap(range1, range2));
        assert!(!DiagnosticsManager::ranges_overlap(range1, range3));
    }
}
