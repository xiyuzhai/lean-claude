//! Command elaboration
//!
//! This module handles the elaboration of top-level commands like
//! import, namespace, def, theorem, etc.

use lean_kernel::{environment::Environment, module::Import, Name};
use lean_syn_expr::{Syntax, SyntaxKind};
use smallvec::smallvec;

use crate::{error::ElabError, namespace::OpenedNamespace, ElabState, Elaborator};

impl Elaborator {
    /// Elaborate a command
    pub fn elaborate_command(&mut self, syntax: &Syntax) -> Result<(), ElabError> {
        match syntax {
            Syntax::Node(node) => match node.kind {
                SyntaxKind::Import => self.elab_import(node),
                SyntaxKind::Namespace => self.elab_namespace(node),
                SyntaxKind::Open => self.elab_open(node),
                SyntaxKind::End => self.elab_end(node),
                SyntaxKind::Section => self.elab_section(node),
                SyntaxKind::Def => self.elab_def(node),
                SyntaxKind::Theorem => self.elab_theorem(node),
                SyntaxKind::Axiom => self.elab_axiom(node),
                SyntaxKind::Constant => self.elab_constant(node),
                SyntaxKind::Variable => self.elab_variable(node),
                SyntaxKind::Universe => self.elab_universe(node),
                SyntaxKind::Inductive => self.elab_inductive(node),
                _ => Err(ElabError::UnsupportedSyntax(node.kind)),
            },
            _ => Err(ElabError::InvalidSyntax(
                "Expected command syntax".to_string(),
            )),
        }
    }

    /// Elaborate import command
    fn elab_import(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // Extract module name from syntax
        if node.children.is_empty() {
            return Err(ElabError::InvalidSyntax(
                "Import requires a module name".to_string(),
            ));
        }

        // Parse the module path
        let module_name = self.parse_module_path(&node.children[0])?;

        // Create import (TODO: handle import options)
        let import = Import::simple(module_name.clone());

        // Add to current module's imports (this would be handled by module loader)
        // For now, just mark it as a pending import
        Err(ElabError::UnsupportedFeature(format!(
            "Import of {} not yet implemented",
            module_name
        )))
    }

    /// Elaborate namespace command
    fn elab_namespace(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        if node.children.is_empty() {
            return Err(ElabError::InvalidSyntax(
                "Namespace requires a name".to_string(),
            ));
        }

        // Parse namespace name
        let ns_name = self.parse_name(&node.children[0])?;

        // Push namespace onto the stack
        self.state_mut().ns_ctx.push_namespace(ns_name);

        Ok(())
    }

    /// Elaborate open command
    fn elab_open(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        if node.children.is_empty() {
            return Err(ElabError::InvalidSyntax(
                "Open requires a namespace name".to_string(),
            ));
        }

        // Parse namespace to open
        let ns_name = self.parse_name(&node.children[0])?;

        // TODO: Handle open options (only, hiding, renaming)
        let opened = OpenedNamespace::new(ns_name);
        self.state_mut().ns_ctx.open_namespace(opened);

        Ok(())
    }

    /// Elaborate end command
    fn elab_end(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // Optional namespace name to verify
        let expected_name = if !node.children.is_empty() {
            Some(self.parse_name(&node.children[0])?)
        } else {
            None
        };

        // Pop namespace
        let popped = self.state_mut().ns_ctx.pop_namespace()?;

        // Verify if name matches
        if let Some(expected) = expected_name {
            if popped != expected {
                return Err(ElabError::NamespaceError(format!(
                    "Expected to end namespace {}, but ended {}",
                    expected, popped
                )));
            }
        }

        Ok(())
    }

    /// Elaborate section command
    fn elab_section(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        let section_name = if !node.children.is_empty() {
            Some(self.parse_name(&node.children[0])?)
        } else {
            None
        };

        self.state_mut().ns_ctx.enter_section(section_name);
        Ok(())
    }

    /// Elaborate def command
    fn elab_def(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // TODO: Implement full def elaboration
        Err(ElabError::UnsupportedFeature(
            "def elaboration not yet implemented".to_string(),
        ))
    }

    /// Elaborate theorem command
    fn elab_theorem(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // TODO: Implement theorem elaboration
        Err(ElabError::UnsupportedFeature(
            "theorem elaboration not yet implemented".to_string(),
        ))
    }

    /// Elaborate axiom command
    fn elab_axiom(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // TODO: Implement axiom elaboration
        Err(ElabError::UnsupportedFeature(
            "axiom elaboration not yet implemented".to_string(),
        ))
    }

    /// Elaborate constant command
    fn elab_constant(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // TODO: Implement constant elaboration
        Err(ElabError::UnsupportedFeature(
            "constant elaboration not yet implemented".to_string(),
        ))
    }

    /// Elaborate variable command
    fn elab_variable(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // TODO: Implement variable elaboration (section variables)
        Err(ElabError::UnsupportedFeature(
            "variable elaboration not yet implemented".to_string(),
        ))
    }

    /// Elaborate universe command
    fn elab_universe(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // TODO: Implement universe variable declaration
        Err(ElabError::UnsupportedFeature(
            "universe elaboration not yet implemented".to_string(),
        ))
    }

    /// Elaborate inductive command
    fn elab_inductive(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // TODO: Implement inductive type elaboration
        Err(ElabError::UnsupportedFeature(
            "inductive elaboration not yet implemented".to_string(),
        ))
    }

    /// Parse a name from syntax
    fn parse_name(&self, syntax: &Syntax) -> Result<Name, ElabError> {
        match syntax {
            Syntax::Atom(atom) => Ok(Name::mk_simple(atom.value.as_str())),
            Syntax::Node(node) if node.kind == SyntaxKind::Identifier => {
                // Handle qualified names
                self.parse_qualified_name(node)
            }
            _ => Err(ElabError::InvalidSyntax("Expected identifier".to_string())),
        }
    }

    /// Parse a qualified name (e.g., Foo.Bar.Baz)
    fn parse_qualified_name(&self, node: &lean_syn_expr::SyntaxNode) -> Result<Name, ElabError> {
        // TODO: Implement proper qualified name parsing
        if let Some(first) = node.children.first() {
            self.parse_name(first)
        } else {
            Err(ElabError::InvalidSyntax("Empty qualified name".to_string()))
        }
    }

    /// Parse a module path
    fn parse_module_path(&self, syntax: &Syntax) -> Result<Name, ElabError> {
        // Module paths are similar to qualified names
        self.parse_name(syntax)
    }
}

/// Elaborate a module's commands
pub fn elaborate_module_commands(
    elaborator: &mut Elaborator,
    syntax: &Syntax,
) -> Result<(), ElabError> {
    match syntax {
        Syntax::Node(node) if node.kind == SyntaxKind::Module => {
            // Elaborate each command in sequence
            for child in &node.children {
                elaborator.elaborate_command(child)?;
            }
            Ok(())
        }
        _ => Err(ElabError::InvalidSyntax(
            "Expected module syntax".to_string(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::environment_ext::init_basic_environment;

    #[test]
    fn test_namespace_command() {
        let mut elaborator = Elaborator::new();
        elaborator.state_mut().set_env(init_basic_environment());

        // Create a namespace command syntax
        let ns_syntax = Syntax::Node(Box::new(lean_syn_expr::SyntaxNode::new(
            SyntaxKind::Namespace,
            lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
            smallvec![Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                lean_syn_expr::SourceRange {
                    start: lean_syn_expr::SourcePos::new(0, 0, 0),
                    end: lean_syn_expr::SourcePos::new(0, 0, 0),
                },
                eterned::BaseCoword::from("Test")
            ))],
        )));

        let result = elaborator.elaborate_command(&ns_syntax);
        assert!(result.is_ok());

        // Check that namespace was pushed
        assert_eq!(
            elaborator.state().ns_ctx.current_namespace(),
            &Name::mk_simple("Test")
        );
    }

    #[test]
    fn test_open_command() {
        let mut elaborator = Elaborator::new();
        elaborator.state_mut().set_env(init_basic_environment());

        // Create an open command syntax
        let open_syntax = Syntax::Node(Box::new(lean_syn_expr::SyntaxNode::new(
            SyntaxKind::Open,
            lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
            smallvec![Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                lean_syn_expr::SourceRange {
                    start: lean_syn_expr::SourcePos::new(0, 0, 0),
                    end: lean_syn_expr::SourcePos::new(0, 0, 0),
                },
                eterned::BaseCoword::from("Std")
            ))],
        )));

        let result = elaborator.elaborate_command(&open_syntax);
        assert!(result.is_ok());

        // Check that namespace resolution now includes Std
        let resolved = elaborator
            .state()
            .ns_ctx
            .resolve_name(&Name::mk_simple("List"));
        assert!(resolved
            .iter()
            .any(|r| r.name == Name::str(Name::mk_simple("Std"), "List")));
    }
}
