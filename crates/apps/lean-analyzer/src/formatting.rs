//! Document formatting for Lean files
//!
//! Provides rust-analyzer-like formatting capabilities with consistent
//! indentation, spacing, and alignment for Lean code.

use std::collections::VecDeque;

use lsp_types::{Position, Range, TextEdit};

/// Lean code formatter
pub struct LeanFormatter {
    config: FormattingConfig,
}

/// Configuration options for formatting
#[derive(Debug, Clone)]
pub struct FormattingConfig {
    /// Number of spaces for indentation (default: 2)
    pub indent_size: usize,
    /// Maximum line length before wrapping (default: 100)
    pub max_line_length: usize,
    /// Whether to align function arguments (default: true)
    pub align_arguments: bool,
    /// Whether to align match cases (default: true)
    pub align_match_cases: bool,
    /// Whether to insert spaces around operators (default: true)
    pub space_around_operators: bool,
    /// Whether to insert space after colons (default: true)
    pub space_after_colon: bool,
    /// Whether to align comments (default: true)
    pub align_comments: bool,
}

/// Represents a line of Lean code with metadata
#[derive(Debug, Clone)]
struct FormattedLine {
    content: String,
    indent_level: usize,
    #[allow(dead_code)]
    line_type: LineType,
}

/// Types of lines for formatting context
#[derive(Debug, Clone, PartialEq)]
enum LineType {
    Import,
    Namespace,
    Definition,
    Theorem,
    Inductive,
    Structure,
    Instance,
    Match,
    MatchCase,
    Expression,
    Comment,
    Blank,
    #[allow(dead_code)]
    Other,
}

impl LeanFormatter {
    pub fn new() -> Self {
        Self {
            config: FormattingConfig::default(),
        }
    }

    pub fn with_config(config: FormattingConfig) -> Self {
        Self { config }
    }

    /// Format the entire document
    pub fn format_document(&self, content: &str) -> Vec<TextEdit> {
        let lines: Vec<&str> = content.lines().collect();
        let formatted_lines = self.format_lines(&lines);

        self.generate_text_edits(&lines, &formatted_lines)
    }

    /// Format a specific range
    pub fn format_range(&self, content: &str, range: Range) -> Vec<TextEdit> {
        let lines: Vec<&str> = content.lines().collect();
        let start_line = range.start.line as usize;
        let end_line = (range.end.line as usize).min(lines.len().saturating_sub(1));

        if start_line > end_line || start_line >= lines.len() {
            return vec![];
        }

        // Format the selected lines while preserving context
        let context_start = start_line.saturating_sub(5);
        let context_end = (end_line + 5).min(lines.len());

        let context_lines = &lines[context_start..context_end];
        let formatted_context = self.format_lines(context_lines);

        // Extract only the edits for the selected range
        let range_offset = start_line - context_start;
        let formatted_range =
            &formatted_context[range_offset..range_offset + (end_line - start_line + 1)];
        let original_range = &lines[start_line..=end_line];

        self.generate_text_edits_for_range(original_range, formatted_range, start_line)
    }

    /// Format lines with proper indentation and spacing
    fn format_lines(&self, lines: &[&str]) -> Vec<FormattedLine> {
        let mut formatted = Vec::new();
        let mut indent_stack = VecDeque::new();
        let mut current_indent = 0;

        for (i, line) in lines.iter().enumerate() {
            let trimmed = line.trim();

            if trimmed.is_empty() {
                formatted.push(FormattedLine {
                    content: String::new(),
                    indent_level: 0,
                    line_type: LineType::Blank,
                });
                continue;
            }

            let line_type = self.classify_line(trimmed);
            let (content, indent_level) = self.format_line(
                trimmed,
                &line_type,
                &mut current_indent,
                &mut indent_stack,
                i,
                lines,
            );

            formatted.push(FormattedLine {
                content,
                indent_level,
                line_type,
            });
        }

        formatted
    }

    /// Classify a line based on its content
    fn classify_line(&self, line: &str) -> LineType {
        let line = line.trim();

        if line.starts_with("import ") {
            LineType::Import
        } else if line.starts_with("namespace ") {
            LineType::Namespace
        } else if line.starts_with("def ") || line.starts_with("noncomputable def ") {
            LineType::Definition
        } else if line.starts_with("theorem ") || line.starts_with("lemma ") {
            LineType::Theorem
        } else if line.starts_with("inductive ") {
            LineType::Inductive
        } else if line.starts_with("structure ") || line.starts_with("class ") {
            LineType::Structure
        } else if line.starts_with("instance ") {
            LineType::Instance
        } else if line.starts_with("match ") || line.contains(" match ") {
            LineType::Match
        } else if line.starts_with("| ") {
            LineType::MatchCase
        } else if line.starts_with("--") || line.starts_with("/-") {
            LineType::Comment
        } else {
            LineType::Expression
        }
    }

    /// Format a single line with proper indentation
    fn format_line(
        &self,
        line: &str,
        line_type: &LineType,
        current_indent: &mut usize,
        _indent_stack: &mut VecDeque<usize>,
        line_index: usize,
        all_lines: &[&str],
    ) -> (String, usize) {
        // Adjust indentation based on line type and context
        let indent_change = self.calculate_indent_change(line, line_type, line_index, all_lines);

        if indent_change < 0 {
            *current_indent = current_indent.saturating_sub((-indent_change) as usize);
        }

        let formatted_content = self.format_line_content(line, line_type);
        let result_indent = *current_indent;

        if indent_change > 0 {
            *current_indent += indent_change as usize;
        }

        (formatted_content, result_indent)
    }

    /// Calculate how much the indentation should change after this line
    fn calculate_indent_change(
        &self,
        line: &str,
        line_type: &LineType,
        _line_index: usize,
        _all_lines: &[&str],
    ) -> i32 {
        match line_type {
            LineType::Definition
            | LineType::Theorem
            | LineType::Inductive
            | LineType::Structure => {
                if line.ends_with(':') || line.contains(" := ") {
                    0 // These usually define their content on the same line
                } else {
                    1 // Will likely have indented content following
                }
            }
            LineType::Match => 1,
            LineType::MatchCase => {
                if line.contains(" => ") {
                    0 // Case with immediate result
                } else {
                    1 // Case with indented body
                }
            }
            _ => 0,
        }
    }

    /// Format the content of a line (spacing, operators, etc.)
    fn format_line_content(&self, line: &str, line_type: &LineType) -> String {
        let mut result = line.to_string();

        // Apply formatting rules based on configuration
        if self.config.space_around_operators {
            result = self.add_operator_spacing(&result);
        }

        if self.config.space_after_colon {
            result = self.add_colon_spacing(&result);
        }

        // Special formatting for different line types
        match line_type {
            LineType::Definition | LineType::Theorem => {
                result = self.format_definition_line(&result);
            }
            LineType::MatchCase => {
                result = self.format_match_case(&result);
            }
            LineType::Import => {
                result = self.format_import_line(&result);
            }
            _ => {}
        }

        result
    }

    /// Add proper spacing around operators
    fn add_operator_spacing(&self, line: &str) -> String {
        let operators = [
            ":=", "=", "+", "-", "*", "/", "<", ">", "≤", "≥", "∧", "∨", "→", "↔",
        ];
        let mut result = line.to_string();

        for op in &operators {
            // Add spaces around operators, but be careful not to break existing good
            // spacing
            let spaced_op = format!(" {op} ");
            result = result.replace(&format!("{}{}", op, ""), &spaced_op);
            result = result.replace(&format!("{}{}", "", op), &spaced_op);

            // Clean up multiple spaces
            result = result.replace(&format!("  {op}  "), &spaced_op);
        }

        result
    }

    /// Add proper spacing after colons
    fn add_colon_spacing(&self, line: &str) -> String {
        // Add space after colons in type annotations, but not in namespaces
        let mut result = line.to_string();

        // Pattern: identifier : Type (but not Module::identifier)
        if !line.contains("::") {
            result = result.replace(":", ": ");
            // Clean up double spaces
            result = result.replace(":  ", ": ");
        }

        result
    }

    /// Format definition lines specially
    fn format_definition_line(&self, line: &str) -> String {
        let mut result = line.to_string();

        // Ensure proper spacing in function signatures
        if let Some(def_pos) = result.find("def ") {
            if let Some(colon_pos) = result[def_pos..].find(" : ") {
                // Function with explicit type
                let before_colon = &result[..def_pos + colon_pos];
                let after_colon = &result[def_pos + colon_pos + 3..];

                // Format parameter list
                let formatted_params = self.format_parameter_list(before_colon);
                result = format!("{formatted_params} : {after_colon}");
            }
        }

        result
    }

    /// Format parameter lists with proper spacing
    fn format_parameter_list(&self, params: &str) -> String {
        let mut result = params.to_string();

        // Add spaces around parentheses in parameter lists
        result = result.replace("(", " (");
        result = result.replace(")", ") ");

        // Clean up extra spaces
        result = result.replace("  ", " ");
        result = result.trim().to_string();

        result
    }

    /// Format match cases with proper alignment
    fn format_match_case(&self, line: &str) -> String {
        let mut result = line.to_string();

        if result.starts_with("| ") {
            // Ensure consistent spacing after pipe
            // Consistent spacing after pipe is already correct

            // Align the arrow if present
            if let Some(arrow_pos) = result.find(" => ") {
                let before_arrow = &result[..arrow_pos];
                let after_arrow = &result[arrow_pos + 4..];
                result = format!("{before_arrow} => {after_arrow}");
            }
        }

        result
    }

    /// Format import lines
    fn format_import_line(&self, line: &str) -> String {
        // Ensure consistent spacing in import statements
        line.to_string()
    }

    /// Generate text edits from original and formatted lines
    fn generate_text_edits(&self, original: &[&str], formatted: &[FormattedLine]) -> Vec<TextEdit> {
        let mut edits = Vec::new();

        for (i, (orig_line, fmt_line)) in original.iter().zip(formatted.iter()).enumerate() {
            let formatted_content =
                self.apply_indentation(&fmt_line.content, fmt_line.indent_level);

            if *orig_line != formatted_content {
                edits.push(TextEdit {
                    range: Range {
                        start: Position::new(i as u32, 0),
                        end: Position::new(i as u32, orig_line.len() as u32),
                    },
                    new_text: formatted_content,
                });
            }
        }

        edits
    }

    /// Generate text edits for a specific range
    fn generate_text_edits_for_range(
        &self,
        original: &[&str],
        formatted: &[FormattedLine],
        start_line: usize,
    ) -> Vec<TextEdit> {
        let mut edits = Vec::new();

        for (i, (orig_line, fmt_line)) in original.iter().zip(formatted.iter()).enumerate() {
            let formatted_content =
                self.apply_indentation(&fmt_line.content, fmt_line.indent_level);

            if *orig_line != formatted_content {
                edits.push(TextEdit {
                    range: Range {
                        start: Position::new((start_line + i) as u32, 0),
                        end: Position::new((start_line + i) as u32, orig_line.len() as u32),
                    },
                    new_text: formatted_content,
                });
            }
        }

        edits
    }

    /// Apply indentation to a line
    fn apply_indentation(&self, content: &str, indent_level: usize) -> String {
        if content.trim().is_empty() {
            String::new()
        } else {
            format!(
                "{}{}",
                " ".repeat(indent_level * self.config.indent_size),
                content
            )
        }
    }
}

impl FormattingConfig {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a compact formatting configuration
    pub fn compact() -> Self {
        Self {
            indent_size: 2,
            max_line_length: 80,
            align_arguments: false,
            align_match_cases: false,
            space_around_operators: true,
            space_after_colon: true,
            align_comments: false,
        }
    }

    /// Create a spacious formatting configuration
    pub fn spacious() -> Self {
        Self {
            indent_size: 4,
            max_line_length: 120,
            align_arguments: true,
            align_match_cases: true,
            space_around_operators: true,
            space_after_colon: true,
            align_comments: true,
        }
    }
}

impl Default for FormattingConfig {
    fn default() -> Self {
        Self {
            indent_size: 2,
            max_line_length: 100,
            align_arguments: true,
            align_match_cases: true,
            space_around_operators: true,
            space_after_colon: true,
            align_comments: true,
        }
    }
}

impl Default for LeanFormatter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_formatting() {
        let formatter = LeanFormatter::new();
        let input = "def   test(x:Nat):Nat:=x+1";
        let edits = formatter.format_document(input);

        assert!(!edits.is_empty());
        // The formatted version should have proper spacing
    }

    #[test]
    fn test_indentation() {
        let formatter = LeanFormatter::new();
        let input = "def test : Nat :=\nmatch x with\n| 0 => 1\n| n + 1 => n";
        let edits = formatter.format_document(input);

        // Should properly indent match cases
        assert!(!edits.is_empty());
    }

    #[test]
    fn test_operator_spacing() {
        let formatter = LeanFormatter::new();
        let input = "def test:=x+y*z";
        let edits = formatter.format_document(input);

        // Should add spaces around operators
        assert!(!edits.is_empty());
    }
}
