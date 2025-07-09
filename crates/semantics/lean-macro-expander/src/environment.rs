use eterned::BaseCoword;
use im::HashMap;
use lean_syn_expr::{Syntax, SyntaxKind};

use crate::error::{ExpansionError, ExpansionResult};

/// A macro definition with its pattern and expansion template
#[derive(Debug, Clone)]
pub struct MacroDefinition {
    /// The name of the macro
    pub name: BaseCoword,
    /// The pattern to match (includes parameter declarations)
    pub pattern: Syntax,
    /// The template to expand to
    pub template: Syntax,
    /// The category this macro produces (e.g., "term", "command")
    pub category: BaseCoword,
    /// Priority for overlapping patterns
    pub priority: i32,
}

/// Environment storing all macro definitions
#[derive(Debug, Clone, Default)]
pub struct MacroEnvironment {
    /// Map from macro names to their definitions
    /// Multiple definitions with the same name are allowed (for macro_rules)
    macros: HashMap<BaseCoword, Vec<MacroDefinition>>,
}

impl MacroEnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a new macro definition
    pub fn register_macro(&mut self, def: MacroDefinition) {
        self.macros.entry(def.name.clone()).or_default().push(def);
    }

    /// Get all macro definitions with a given name
    pub fn get_macros(&self, name: &str) -> Option<&[MacroDefinition]> {
        self.macros
            .get(&BaseCoword::new(name))
            .map(|v| v.as_slice())
    }

    /// Check if a macro exists
    pub fn has_macro(&self, name: &str) -> bool {
        self.macros.contains_key(&BaseCoword::new(name))
    }

    /// Check if there are any registered macros
    pub fn has_any_macros(&self) -> bool {
        !self.macros.is_empty()
    }

    /// Create a macro definition from parsed syntax
    pub fn create_macro_from_syntax(syntax: &Syntax) -> ExpansionResult<MacroDefinition> {
        match syntax {
            Syntax::Node(node) if node.kind == SyntaxKind::MacroDef => {
                // Extract components from macro definition
                // Expected structure: MacroDef [name, pattern, category, template]
                // Based on test output: twice, (App x term), term, (SyntaxQuotation ...)

                if node.children.len() < 3 {
                    return Err(ExpansionError::InvalidMacroDefinition {
                        message: "Macro definition requires at least 3 components".to_string(),
                        range: node.range,
                    });
                }

                let mut idx = 0;
                let mut name = BaseCoword::new("anonymous");

                let mut category = BaseCoword::new("term");

                // First element might be name or pattern
                if let Syntax::Atom(atom) = &node.children[idx] {
                    // It's a name
                    name = atom.value.clone();
                    idx += 1;
                }

                // Next is pattern
                if idx >= node.children.len() {
                    return Err(ExpansionError::InvalidMacroDefinition {
                        message: "Missing pattern".to_string(),
                        range: node.range,
                    });
                }
                let pattern = node.children[idx].clone();
                idx += 1;

                // Next might be category or template
                if idx < node.children.len() - 1 {
                    // We have both category and template
                    if let Syntax::Atom(cat) = &node.children[idx] {
                        category = cat.value.clone();
                        idx += 1;
                    }
                }

                // Last element is template
                if idx >= node.children.len() {
                    return Err(ExpansionError::InvalidMacroDefinition {
                        message: "Missing template".to_string(),
                        range: node.range,
                    });
                }
                let template = node.children[idx].clone();

                Ok(MacroDefinition {
                    name,
                    pattern,
                    template,
                    category,
                    priority: 0,
                })
            }
            _ => Err(ExpansionError::InvalidMacroDefinition {
                message: "Expected MacroDef node".to_string(),
                range: syntax
                    .range()
                    .cloned()
                    .unwrap_or(lean_syn_expr::SourceRange {
                        start: lean_syn_expr::SourcePos::new(0, 0, 0),
                        end: lean_syn_expr::SourcePos::new(0, 0, 0),
                    }),
            }),
        }
    }
}
