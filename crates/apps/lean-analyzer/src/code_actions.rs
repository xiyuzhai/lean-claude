//! Code actions and quick fixes for lean-analyzer
//!
//! This module provides rust-analyzer-like quick fixes, refactoring
//! suggestions, and code actions to improve the Lean development experience.

use lsp_types::{
    CodeAction, CodeActionKind, CodeActionOrCommand, CodeActionParams, Position, Range, TextEdit,
    Url, WorkspaceEdit,
};
use serde_json::Value;

/// Manages code actions and quick fixes
pub struct CodeActionProvider {
    common_imports: CommonImports,
}

/// Common Lean imports for quick fixes
struct CommonImports {
    nat_imports: Vec<&'static str>,
    list_imports: Vec<&'static str>,
    string_imports: Vec<&'static str>,
    io_imports: Vec<&'static str>,
}

/// Types of code actions we can provide
#[derive(Debug, Clone)]
pub enum ActionType {
    QuickFix,
    Refactor,
    Source,
    Extract,
    Inline,
    Generate,
}

impl CodeActionProvider {
    pub fn new() -> Self {
        Self {
            common_imports: CommonImports::new(),
        }
    }

    /// Get code actions for a given range and context
    pub fn get_code_actions(
        &self,
        params: &CodeActionParams,
        file_content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Add quick fixes for diagnostics
        for diagnostic in &params.context.diagnostics {
            if let Some(quick_fixes) = self.get_quick_fixes_for_diagnostic(
                diagnostic,
                &params.text_document.uri,
                file_content,
            ) {
                actions.extend(quick_fixes);
            }
        }

        // Add refactoring actions
        actions.extend(self.get_refactoring_actions(params, file_content));

        // Add source actions (imports, formatting, etc.)
        actions.extend(self.get_source_actions(params, file_content));

        actions
    }

    /// Get quick fixes for a specific diagnostic
    fn get_quick_fixes_for_diagnostic(
        &self,
        diagnostic: &lsp_types::Diagnostic,
        uri: &Url,
        file_content: &str,
    ) -> Option<Vec<CodeActionOrCommand>> {
        let mut actions = Vec::new();

        // Parse diagnostic data for suggestions
        if let Some(data) = &diagnostic.data {
            if let Ok(enhanced_data) = serde_json::from_value::<Value>(data.clone()) {
                if let Some(suggestions) = enhanced_data.get("suggestions") {
                    if let Some(suggestions_array) = suggestions.as_array() {
                        for suggestion in suggestions_array {
                            if let Some(action) =
                                self.suggestion_to_code_action(suggestion, uri, &diagnostic.message)
                            {
                                actions.push(action);
                            }
                        }
                    }
                }
            }
        }

        // Generate common quick fixes based on error patterns
        actions.extend(self.generate_common_quick_fixes(diagnostic, uri, file_content));

        if actions.is_empty() {
            None
        } else {
            Some(actions)
        }
    }

    /// Generate common quick fixes based on error patterns
    fn generate_common_quick_fixes(
        &self,
        diagnostic: &lsp_types::Diagnostic,
        uri: &Url,
        file_content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();
        let message = &diagnostic.message;

        // Missing import fixes
        if message.contains("Unknown identifier") || message.contains("not found") {
            actions.extend(self.suggest_imports(diagnostic, uri, file_content));
        }

        // Type annotation fixes
        if message.contains("type mismatch") || message.contains("Cannot infer type") {
            actions.extend(self.suggest_type_annotations(diagnostic, uri, file_content));
        }

        // Syntax fixes
        if message.contains("Expected") {
            actions.extend(self.suggest_syntax_fixes(diagnostic, uri, file_content));
        }

        // Namespace fixes
        if message.contains("namespace") || message.contains("open") {
            actions.extend(self.suggest_namespace_fixes(diagnostic, uri, file_content));
        }

        actions
    }

    /// Suggest import fixes
    fn suggest_imports(
        &self,
        diagnostic: &lsp_types::Diagnostic,
        uri: &Url,
        _file_content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();
        let message = &diagnostic.message;

        // Extract identifier from error message
        if let Some(identifier) = self.extract_identifier_from_error(message) {
            for import in self.common_imports.get_imports_for(&identifier) {
                let action = CodeAction {
                    title: format!("Import {import}"),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: Some(vec![diagnostic.clone()]),
                    edit: Some(self.create_import_edit(uri, import)),
                    command: None,
                    is_preferred: Some(true),
                    disabled: None,
                    data: None,
                };
                actions.push(CodeActionOrCommand::CodeAction(action));
            }
        }

        actions
    }

    /// Suggest type annotations
    fn suggest_type_annotations(
        &self,
        diagnostic: &lsp_types::Diagnostic,
        uri: &Url,
        file_content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Extract context from the error location
        let line_content = self.get_line_content(file_content, diagnostic.range.start.line);

        // Suggest common type annotations
        if line_content.contains("def ") && !line_content.contains(" : ") {
            let action = CodeAction {
                title: "Add explicit return type".to_string(),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(self.create_type_annotation_edit(uri, &diagnostic.range)),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            };
            actions.push(CodeActionOrCommand::CodeAction(action));
        }

        actions
    }

    /// Suggest syntax fixes
    fn suggest_syntax_fixes(
        &self,
        diagnostic: &lsp_types::Diagnostic,
        uri: &Url,
        file_content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();
        let message = &diagnostic.message;

        // Common syntax error patterns
        if message.contains("Expected '('") {
            actions.push(self.create_syntax_fix_action(
                "Add missing parentheses",
                diagnostic,
                uri,
                "(",
            ));
        }

        if message.contains("Expected ':'") {
            actions.push(self.create_syntax_fix_action(
                "Add missing colon",
                diagnostic,
                uri,
                " : ",
            ));
        }

        if message.contains("Expected 'def'") {
            let line_content = self.get_line_content(file_content, diagnostic.range.start.line);
            if line_content.trim_start().starts_with("function") {
                actions.push(self.create_syntax_fix_action(
                    "Replace 'function' with 'def'",
                    diagnostic,
                    uri,
                    "def",
                ));
            }
        }

        actions
    }

    /// Suggest namespace fixes
    fn suggest_namespace_fixes(
        &self,
        diagnostic: &lsp_types::Diagnostic,
        uri: &Url,
        _file_content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Suggest opening common namespaces
        let common_namespaces = ["List", "Array", "String", "Nat", "IO"];

        for ns in &common_namespaces {
            let action = CodeAction {
                title: format!("Open namespace {ns}"),
                kind: Some(CodeActionKind::QUICKFIX),
                diagnostics: Some(vec![diagnostic.clone()]),
                edit: Some(self.create_namespace_edit(uri, ns)),
                command: None,
                is_preferred: Some(false),
                disabled: None,
                data: None,
            };
            actions.push(CodeActionOrCommand::CodeAction(action));
        }

        actions
    }

    /// Get refactoring actions
    fn get_refactoring_actions(
        &self,
        params: &CodeActionParams,
        file_content: &str,
    ) -> Vec<CodeActionOrCommand> {
        let mut actions = Vec::new();

        // Extract function/definition
        if self.can_extract_function(&params.range, file_content) {
            let action = CodeAction {
                title: "Extract function".to_string(),
                kind: Some(CodeActionKind::REFACTOR_EXTRACT),
                diagnostics: None,
                edit: None, // Would need more sophisticated analysis
                command: Some(lsp_types::Command {
                    title: "Extract function".to_string(),
                    command: "lean-analyzer.extractFunction".to_string(),
                    arguments: Some(vec![
                        serde_json::to_value(&params.text_document.uri).unwrap(),
                        serde_json::to_value(params.range).unwrap(),
                    ]),
                }),
                is_preferred: Some(false),
                disabled: None,
                data: None,
            };
            actions.push(CodeActionOrCommand::CodeAction(action));
        }

        // Rename symbol
        actions.push(CodeActionOrCommand::CodeAction(CodeAction {
            title: "Rename symbol".to_string(),
            kind: Some(CodeActionKind::REFACTOR),
            diagnostics: None,
            edit: None,
            command: Some(lsp_types::Command {
                title: "Rename symbol".to_string(),
                command: "lean-analyzer.rename".to_string(),
                arguments: Some(vec![
                    serde_json::to_value(&params.text_document.uri).unwrap(),
                    serde_json::to_value(params.range.start).unwrap(),
                ]),
            }),
            is_preferred: Some(false),
            disabled: None,
            data: None,
        }));

        actions
    }

    /// Get source actions (organize imports, format, etc.)
    fn get_source_actions(
        &self,
        params: &CodeActionParams,
        _file_content: &str,
    ) -> Vec<CodeActionOrCommand> {
        vec![
            // Organize imports
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Organize imports".to_string(),
                kind: Some(CodeActionKind::SOURCE_ORGANIZE_IMPORTS),
                diagnostics: None,
                edit: None,
                command: Some(lsp_types::Command {
                    title: "Organize imports".to_string(),
                    command: "lean-analyzer.organizeImports".to_string(),
                    arguments: Some(vec![
                        serde_json::to_value(&params.text_document.uri).unwrap()
                    ]),
                }),
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
            // Format document
            CodeActionOrCommand::CodeAction(CodeAction {
                title: "Format document".to_string(),
                kind: Some(CodeActionKind::SOURCE),
                diagnostics: None,
                edit: None,
                command: Some(lsp_types::Command {
                    title: "Format document".to_string(),
                    command: "lean-analyzer.formatDocument".to_string(),
                    arguments: Some(vec![
                        serde_json::to_value(&params.text_document.uri).unwrap()
                    ]),
                }),
                is_preferred: Some(false),
                disabled: None,
                data: None,
            }),
        ]
    }

    // Helper methods

    fn suggestion_to_code_action(
        &self,
        suggestion: &Value,
        uri: &Url,
        diagnostic_message: &str,
    ) -> Option<CodeActionOrCommand> {
        let range = suggestion.get("range")?;
        let replacement = suggestion.get("replacement")?.as_str()?;
        let description = suggestion.get("description")?.as_str()?;

        let range: Range = serde_json::from_value(range.clone()).ok()?;

        let edit = WorkspaceEdit {
            changes: Some(
                [(
                    uri.clone(),
                    vec![TextEdit {
                        range,
                        new_text: replacement.to_string(),
                    }],
                )]
                .into_iter()
                .collect(),
            ),
            document_changes: None,
            change_annotations: None,
        };

        let action = CodeAction {
            title: description.to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: Some(vec![lsp_types::Diagnostic {
                range,
                severity: Some(lsp_types::DiagnosticSeverity::ERROR),
                code: None,
                code_description: None,
                source: Some("lean-analyzer".to_string()),
                message: diagnostic_message.to_string(),
                related_information: None,
                tags: None,
                data: None,
            }]),
            edit: Some(edit),
            command: None,
            is_preferred: Some(true),
            disabled: None,
            data: None,
        };

        Some(CodeActionOrCommand::CodeAction(action))
    }

    fn extract_identifier_from_error(&self, message: &str) -> Option<String> {
        // Extract identifier from error messages like "Unknown identifier 'Nat'"
        if let Some(start) = message.find('\'') {
            if let Some(end) = message[start + 1..].find('\'') {
                return Some(message[start + 1..start + 1 + end].to_string());
            }
        }
        None
    }

    fn create_import_edit(&self, uri: &Url, import: &str) -> WorkspaceEdit {
        // Insert import at the top of the file
        WorkspaceEdit {
            changes: Some(
                [(
                    uri.clone(),
                    vec![TextEdit {
                        range: Range {
                            start: Position::new(0, 0),
                            end: Position::new(0, 0),
                        },
                        new_text: format!("import {import}\n"),
                    }],
                )]
                .into_iter()
                .collect(),
            ),
            document_changes: None,
            change_annotations: None,
        }
    }

    fn create_type_annotation_edit(&self, uri: &Url, range: &Range) -> WorkspaceEdit {
        // This is a simplified implementation - would need type inference
        WorkspaceEdit {
            changes: Some(
                [(
                    uri.clone(),
                    vec![TextEdit {
                        range: Range {
                            start: range.end,
                            end: range.end,
                        },
                        new_text: " : α".to_string(), // Placeholder - would infer actual type
                    }],
                )]
                .into_iter()
                .collect(),
            ),
            document_changes: None,
            change_annotations: None,
        }
    }

    fn create_syntax_fix_action(
        &self,
        title: &str,
        diagnostic: &lsp_types::Diagnostic,
        uri: &Url,
        replacement: &str,
    ) -> CodeActionOrCommand {
        let edit = WorkspaceEdit {
            changes: Some(
                [(
                    uri.clone(),
                    vec![TextEdit {
                        range: diagnostic.range,
                        new_text: replacement.to_string(),
                    }],
                )]
                .into_iter()
                .collect(),
            ),
            document_changes: None,
            change_annotations: None,
        };

        CodeActionOrCommand::CodeAction(CodeAction {
            title: title.to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: Some(vec![diagnostic.clone()]),
            edit: Some(edit),
            command: None,
            is_preferred: Some(true),
            disabled: None,
            data: None,
        })
    }

    fn create_namespace_edit(&self, uri: &Url, namespace: &str) -> WorkspaceEdit {
        WorkspaceEdit {
            changes: Some(
                [(
                    uri.clone(),
                    vec![TextEdit {
                        range: Range {
                            start: Position::new(0, 0),
                            end: Position::new(0, 0),
                        },
                        new_text: format!("open {namespace}\n"),
                    }],
                )]
                .into_iter()
                .collect(),
            ),
            document_changes: None,
            change_annotations: None,
        }
    }

    fn get_line_content(&self, file_content: &str, line: u32) -> String {
        file_content
            .lines()
            .nth(line as usize)
            .unwrap_or("")
            .to_string()
    }

    fn can_extract_function(&self, range: &Range, file_content: &str) -> bool {
        // Simple heuristic - check if selection contains multiple statements
        let start_line = range.start.line as usize;
        let end_line = range.end.line as usize;

        if start_line >= end_line {
            return false;
        }

        let lines: Vec<&str> = file_content.lines().collect();
        if end_line >= lines.len() {
            return false;
        }

        // Check if the selection contains meaningful code
        let selected_lines = &lines[start_line..=end_line];
        let non_empty_lines: Vec<_> = selected_lines
            .iter()
            .filter(|line| !line.trim().is_empty())
            .collect();

        non_empty_lines.len() >= 2
    }
}

impl CommonImports {
    fn new() -> Self {
        Self {
            nat_imports: vec!["Std.Init.Data.Nat", "Mathlib.Data.Nat.Basic"],
            list_imports: vec!["Std.Data.List.Basic", "Mathlib.Data.List.Basic"],
            string_imports: vec!["Std.Data.String.Basic"],
            io_imports: vec!["Std.IO", "Std.IO.FS"],
        }
    }

    fn get_imports_for(&self, identifier: &str) -> Vec<&'static str> {
        match identifier {
            "Nat" | "ℕ" => self.nat_imports.clone(),
            "List" => self.list_imports.clone(),
            "String" => self.string_imports.clone(),
            "IO" | "println!" => self.io_imports.clone(),
            "Array" => vec!["Std.Data.Array.Basic"],
            "HashMap" => vec!["Std.Data.HashMap"],
            "Set" => vec!["Std.Data.Set.Basic"],
            "Option" => vec!["Std.Init.Data.Option.Basic"],
            "Result" => vec!["Std.Init.Data.Result"],
            _ => vec![],
        }
    }
}

impl Default for CodeActionProvider {
    fn default() -> Self {
        Self::new()
    }
}
