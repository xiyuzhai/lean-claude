use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};

use crate::{
    environment::MacroEnvironment,
    error::{ExpansionError, ExpansionResult},
    hygiene::HygieneContext,
    pattern::{substitute_template, PatternMatcher},
};

/// Main macro expander
pub struct MacroExpander {
    env: MacroEnvironment,
    hygiene: HygieneContext,
}

impl MacroExpander {
    pub fn new(env: MacroEnvironment) -> Self {
        Self {
            env,
            hygiene: HygieneContext::new(),
        }
    }

    /// Expand all macros in a syntax tree
    pub fn expand(&mut self, syntax: &Syntax) -> ExpansionResult<Syntax> {
        self.expand_with_context(syntax, &self.hygiene.clone())
    }

    fn expand_with_context(
        &mut self,
        syntax: &Syntax,
        ctx: &HygieneContext,
    ) -> ExpansionResult<Syntax> {
        // Check expansion depth
        let new_ctx = ctx
            .enter_expansion()
            .ok_or(ExpansionError::ExpansionLimitExceeded {
                limit: ctx.max_depth,
            })?;

        match syntax {
            Syntax::Node(node) => {
                // Check if this is a macro application
                if let Some(expanded) = self.try_expand_macro(node, &new_ctx)? {
                    // Recursively expand the result
                    self.expand_with_context(&expanded, &new_ctx)
                } else {
                    // Not a macro, recursively expand children
                    self.expand_node(node, &new_ctx)
                }
            }
            // Atoms and missing are returned as-is
            _ => Ok(syntax.clone()),
        }
    }

    /// Try to expand a node as a macro application
    fn try_expand_macro(
        &self,
        node: &SyntaxNode,
        _ctx: &HygieneContext,
    ) -> ExpansionResult<Option<Syntax>> {
        // Check if this looks like a macro application
        if node.kind != SyntaxKind::App {
            return Ok(None);
        }

        // Get the head of the application
        let head = match node.children.first() {
            Some(Syntax::Atom(atom)) => atom,
            _ => return Ok(None),
        };

        // Look up macro definitions
        let macro_name = head.value.as_str();
        let macros = match self.env.get_macros(macro_name) {
            Some(macros) => macros,
            None => return Ok(None),
        };

        // Try each macro definition in order
        for macro_def in macros {
            // For macro applications, we need to match the arguments against the pattern
            // If we have (App twice 5) and pattern x:term, we should match 5 against x:term

            // Get the arguments (everything after the macro name)
            let args = if node.children.len() > 1 {
                &node.children[1..]
            } else {
                // No arguments
                &[]
            };

            // Try to match the pattern against the arguments
            let match_target = if args.len() == 1 {
                // Single argument - match directly
                &args[0]
            } else if args.is_empty() {
                // No arguments - create an empty syntax
                &Syntax::Missing
            } else {
                // Multiple arguments - wrap in an App node
                &Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::App,
                    range: node.range,
                    children: args.to_vec().into(),
                }))
            };

            if let Some(pattern_match) =
                PatternMatcher::match_pattern(&macro_def.pattern, match_target)?
            {
                // Substitute into template
                let expanded = substitute_template(&macro_def.template, &pattern_match.bindings)?;
                return Ok(Some(expanded));
            }
        }

        // No matching macro found
        Ok(None)
    }

    /// Expand children of a node
    fn expand_node(&mut self, node: &SyntaxNode, ctx: &HygieneContext) -> ExpansionResult<Syntax> {
        let mut new_children = Vec::with_capacity(node.children.len());

        for child in &node.children {
            new_children.push(self.expand_with_context(child, ctx)?);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: node.kind,
            range: node.range,
            children: new_children.into(),
        })))
    }

    /// Register built-in macros
    pub fn register_builtins(&mut self) {
        // TODO: Add built-in macros like panic!, assert!, etc.
    }
}
