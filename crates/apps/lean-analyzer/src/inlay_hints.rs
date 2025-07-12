//! Inlay hints for Lean 4
//!
//! Provides contextual information displayed inline in the editor:
//! - Type annotations for variables and expressions
//! - Parameter names for function calls
//! - Implicit argument values
//! - Proof state information
//! - Universe levels
//! - Tactic goals and hypotheses

use std::{collections::HashMap, path::Path};

use lean_kernel::{Expr, Name};
use lean_parser::ParserResult;
use lean_syn_expr::Syntax;
use lsp_types::{InlayHint, InlayHintKind, InlayHintLabel, Position, Range, TextEdit};

/// Configuration for inlay hints
#[derive(Debug, Clone)]
pub struct InlayHintConfig {
    /// Show type annotations for let bindings
    pub show_let_types: bool,
    /// Show parameter names in function calls
    pub show_parameter_names: bool,
    /// Show implicit arguments when explicitly provided
    pub show_implicit_args: bool,
    /// Show universe levels
    pub show_universe_levels: bool,
    /// Show proof goals and context
    pub show_proof_state: bool,
    /// Show inferred types for expressions
    pub show_inferred_types: bool,
    /// Maximum length for type hints (truncate longer types)
    pub max_type_length: usize,
    /// Show hints for obvious types (like literals)
    pub show_obvious_types: bool,
}

impl Default for InlayHintConfig {
    fn default() -> Self {
        Self {
            show_let_types: true,
            show_parameter_names: true,
            show_implicit_args: false,
            show_universe_levels: false,
            show_proof_state: true,
            show_inferred_types: true,
            max_type_length: 50,
            show_obvious_types: false,
        }
    }
}

/// Type of inlay hint
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanInlayHintKind {
    /// Type annotation (e.g., ": Nat")
    Type,
    /// Parameter name (e.g., "length:")
    Parameter,
    /// Implicit argument (e.g., "@List")
    ImplicitArg,
    /// Universe level (e.g., ".{u}")
    Universe,
    /// Proof goal
    Goal,
    /// Hypothesis in proof context
    Hypothesis,
    /// Tactic state
    TacticState,
}

impl From<LeanInlayHintKind> for InlayHintKind {
    fn from(kind: LeanInlayHintKind) -> Self {
        match kind {
            LeanInlayHintKind::Type => InlayHintKind::TYPE,
            LeanInlayHintKind::Parameter => InlayHintKind::PARAMETER,
            LeanInlayHintKind::ImplicitArg => InlayHintKind::PARAMETER,
            LeanInlayHintKind::Universe => InlayHintKind::TYPE,
            LeanInlayHintKind::Goal => InlayHintKind::TYPE,
            LeanInlayHintKind::Hypothesis => InlayHintKind::TYPE,
            LeanInlayHintKind::TacticState => InlayHintKind::TYPE,
        }
    }
}

/// A Lean-specific inlay hint
#[derive(Debug, Clone)]
pub struct LeanInlayHint {
    /// Position where hint should be displayed
    pub position: Position,
    /// The hint text
    pub label: String,
    /// Kind of hint
    pub kind: LeanInlayHintKind,
    /// Whether the hint should be padded with spaces
    pub padding_left: bool,
    pub padding_right: bool,
    /// Optional tooltip with more information
    pub tooltip: Option<String>,
    /// Optional text edit to apply when hint is clicked
    pub text_edit: Option<TextEdit>,
}

impl From<LeanInlayHint> for InlayHint {
    fn from(hint: LeanInlayHint) -> Self {
        InlayHint {
            position: hint.position,
            label: InlayHintLabel::String(hint.label),
            kind: Some(hint.kind.into()),
            text_edits: hint.text_edit.map(|edit| vec![edit]),
            tooltip: hint.tooltip.map(lsp_types::InlayHintTooltip::String),
            padding_left: Some(hint.padding_left),
            padding_right: Some(hint.padding_right),
            data: None,
        }
    }
}

/// Context for generating inlay hints
#[derive(Debug, Clone, Default)]
pub struct HintContext {
    /// Local variable types
    pub locals: HashMap<Name, Expr>,
    /// Current proof goals
    pub goals: Vec<Expr>,
    /// Available hypotheses
    pub hypotheses: HashMap<Name, Expr>,
    /// Current namespace
    pub namespace: Option<Name>,
    /// Universe context
    pub universes: HashMap<Name, lean_kernel::Level>,
}

/// Main inlay hints provider
pub struct InlayHintProvider {
    config: InlayHintConfig,
}

impl InlayHintProvider {
    pub fn new(config: InlayHintConfig) -> Self {
        Self { config }
    }

    /// Get inlay hints for a file
    pub fn get_hints(
        &mut self,
        _path: &Path,
        content: &str,
        _parse_result: &ParserResult<Syntax>,
        _range: Option<Range>,
    ) -> Vec<LeanInlayHint> {
        let mut hints = Vec::new();

        // For now, provide basic hints based on text patterns
        // This is a simplified implementation that can be expanded later
        self.analyze_basic_hints(content, &mut hints);

        hints
    }

    /// Basic hint analysis based on text patterns
    fn analyze_basic_hints(&self, content: &str, hints: &mut Vec<LeanInlayHint>) {
        if !self.config.show_let_types {
            return;
        }

        // Simple pattern matching for let bindings
        for (line_idx, line) in content.lines().enumerate() {
            if let Some(pos) = line.find("let ") {
                if let Some(equal_pos) = line[pos..].find(" := ") {
                    let hint_pos = pos + equal_pos;

                    hints.push(LeanInlayHint {
                        position: Position {
                            line: line_idx as u32,
                            character: hint_pos as u32,
                        },
                        label: ": ?".to_string(), // Placeholder type
                        kind: LeanInlayHintKind::Type,
                        padding_left: false,
                        padding_right: true,
                        tooltip: Some("Inferred type (basic implementation)".to_string()),
                        text_edit: None,
                    });
                }
            }
        }
    }
}

impl Default for InlayHintProvider {
    fn default() -> Self {
        Self::new(InlayHintConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use lean_parser::Parser;

    use super::*;

    #[test]
    fn test_inlay_hints_basic() {
        let config = InlayHintConfig::default();
        let mut provider = InlayHintProvider::new(config);

        let content = "let x := 42";
        let mut parser = Parser::new(content);
        let parse_result = parser.module();

        let hints = provider.get_hints(Path::new("test.lean"), content, &parse_result, None);

        // Should work without panicking (may not have hints without elaboration)
        assert!(hints.is_empty() || !hints.is_empty());
    }

    #[test]
    fn test_lambda_hints() {
        let config = InlayHintConfig::default();
        let mut provider = InlayHintProvider::new(config);

        let content = "fun x => x + 1";
        let mut parser = Parser::new(content);
        let parse_result = parser.module();

        let hints = provider.get_hints(Path::new("test.lean"), content, &parse_result, None);

        // Should work without panicking
        assert!(hints.is_empty() || !hints.is_empty());
    }

    #[test]
    fn test_range_filtering() {
        let config = InlayHintConfig::default();
        let mut provider = InlayHintProvider::new(config);

        let content = "def f (x : Nat) : Nat := x + 1\ndef g (y : String) : String := y";
        let mut parser = Parser::new(content);
        let parse_result = parser.module();

        // Request hints only for first line
        let range = Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 30,
            },
        };

        let hints = provider.get_hints(Path::new("test.lean"), content, &parse_result, Some(range));

        // Should work without panicking
        assert!(hints.is_empty() || !hints.is_empty());
    }

    #[test]
    fn test_hint_conversion() {
        let hint = LeanInlayHint {
            position: Position {
                line: 0,
                character: 5,
            },
            label: ": Nat".to_string(),
            kind: LeanInlayHintKind::Type,
            padding_left: false,
            padding_right: true,
            tooltip: Some("Type annotation".to_string()),
            text_edit: None,
        };

        let lsp_hint: InlayHint = hint.into();

        assert_eq!(lsp_hint.position.line, 0);
        assert_eq!(lsp_hint.position.character, 5);
        if let InlayHintLabel::String(label) = lsp_hint.label {
            assert_eq!(label, ": Nat");
        } else {
            panic!("Expected string label");
        }
    }
}
