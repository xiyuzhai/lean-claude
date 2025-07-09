//! Macro expansion integration for the parser

use lean_macro_expander::{MacroEnvironment, MacroExpander};
use lean_syn_expr::{Syntax, SyntaxKind};

use crate::parser::Parser;

/// Parser with macro expansion capabilities
pub struct ExpandingParser<'a> {
    parser: Parser<'a>,
    env: MacroEnvironment,
    expander: Option<MacroExpander>,
}

impl<'a> ExpandingParser<'a> {
    /// Create a new expanding parser
    pub fn new(input: &'a str) -> Self {
        Self {
            parser: Parser::new(input),
            env: MacroEnvironment::new(),
            expander: None,
        }
    }

    /// Parse a module with macro expansion
    pub fn parse_module(&mut self) -> crate::parser::ParserResult<Syntax> {
        // First pass: parse the module
        let module = self.parser.module()?;

        // Collect macro definitions
        self.collect_macros(&module);

        // Create expander if we have macros
        if self.env.has_any_macros() {
            let expander = MacroExpander::new(self.env.clone());
            self.expander = Some(expander);
        }

        // Expand macros if we have an expander
        if let Some(expander) = &mut self.expander {
            expander.expand(&module).map_err(|e| {
                crate::error::ParseError::boxed(
                    crate::error::ParseErrorKind::MacroExpansionError(format!("{e:?}")),
                    self.parser.position(),
                )
            })
        } else {
            Ok(module)
        }
    }

    /// Collect macro definitions from a syntax tree
    fn collect_macros(&mut self, syntax: &Syntax) {
        if let Syntax::Node(node) = syntax {
            // Check if this is a macro definition
            if node.kind == SyntaxKind::MacroDef {
                if let Ok(macro_def) = MacroEnvironment::create_macro_from_syntax(syntax) {
                    self.env.register_macro(macro_def);
                }
            }

            // Recursively collect from children
            for child in &node.children {
                self.collect_macros(child);
            }
        }
    }
}
