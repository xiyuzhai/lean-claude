//! Command elaboration
//!
//! This module handles the elaboration of top-level commands like
//! import, namespace, def, theorem, etc.

use lean_kernel::{environment::Environment, module::Import, Expr, Level, Name};
use lean_syn_expr::{Syntax, SyntaxKind};
use smallvec::smallvec;
use std::{collections::HashMap, sync::Arc};

use crate::{error::ElabError, namespace::OpenedNamespace, module_loader::ModuleLoader, ElabState, Elaborator};

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

        // Parse import options
        let import = self.parse_import_options(node, module_name.clone())?;

        // Get the module loader from state
        let loader = &self.state().module_loader;
        
        // Get current environment or create a new one
        let base_env = self.state().env.clone().unwrap_or_else(Environment::new);
        
        // Load and elaborate the imported module
        let imported_env = loader.elaborate_module(&module_name, base_env.clone())?;
        
        // Merge the imported environment into our current environment
        let merged_env = loader.merge_environments(base_env, &imported_env, &import)?;
        
        // Update our environment
        self.state_mut().set_env(merged_env);
        
        // Open the imported namespace if needed (based on import options)
        // For now, just make the imported names available
        self.state_mut().ns_ctx.open_namespace(OpenedNamespace::new(module_name));
        
        Ok(())
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
        use crate::environment_ext::add_definition;

        if node.children.len() < 3 {
            return Err(ElabError::InvalidSyntax(
                "Def requires name, parameters/type, and value".to_string(),
            ));
        }

        // Parse the definition name
        let name_syntax = &node.children[0];
        let def_name = self.parse_name(name_syntax)?;

        // Make the name absolute in the current namespace
        let full_name = Name::join_relative(self.state().ns_ctx.current_namespace(), &def_name);

        // TODO: Parse parameters and type annotations
        // For now, we'll use a simplified approach

        // Find the value (after :=)
        let mut value_idx = None;
        for (i, child) in node.children.iter().enumerate() {
            if let Syntax::Atom(atom) = child {
                if atom.value.as_str() == ":=" && i + 1 < node.children.len() {
                    value_idx = Some(i + 1);
                    break;
                }
            }
        }

        let value_syntax = match value_idx {
            Some(idx) => &node.children[idx],
            None => return Err(ElabError::InvalidSyntax("Def missing := value".to_string())),
        };

        // Elaborate the value
        let value = self.elaborate(value_syntax)?;

        // Infer the type of the value
        let ty = self.infer_type(&value)?;

        // Add the definition to the environment
        if let Some(env) = &mut self.state_mut().env {
            add_definition(env, full_name.clone(), ty, Some(value), vec![])?;

            // Add to exports if public
            // TODO: Check visibility modifiers
            self.state_mut().ns_ctx.add_export(full_name);
        }

        Ok(())
    }

    /// Elaborate theorem command
    fn elab_theorem(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        use crate::environment_ext::add_definition;

        if node.children.len() < 4 {
            return Err(ElabError::InvalidSyntax(
                "Theorem requires name, type, and proof".to_string(),
            ));
        }

        // Parse the theorem name
        let name_syntax = &node.children[0];
        let thm_name = self.parse_name(name_syntax)?;

        // Make the name absolute in the current namespace
        let full_name = Name::join_relative(self.state().ns_ctx.current_namespace(), &thm_name);

        // Find the type (after :)
        let mut type_idx = None;
        let mut proof_idx = None;

        for (i, child) in node.children.iter().enumerate() {
            if let Syntax::Atom(atom) = child {
                if atom.value.as_str() == ":" && type_idx.is_none() {
                    type_idx = Some(i + 1);
                } else if atom.value.as_str() == ":=" && i + 1 < node.children.len() {
                    proof_idx = Some(i + 1);
                    break;
                }
            }
        }

        let type_syntax = match type_idx {
            Some(idx) if idx < node.children.len() => &node.children[idx],
            _ => return Err(ElabError::InvalidSyntax("Theorem missing type".to_string())),
        };

        let proof_syntax = match proof_idx {
            Some(idx) => &node.children[idx],
            None => {
                return Err(ElabError::InvalidSyntax(
                    "Theorem missing := proof".to_string(),
                ))
            }
        };

        // Elaborate the type
        let ty = self.elaborate(type_syntax)?;

        // Elaborate the proof with the expected type
        let proof = self.elaborate_with_type(proof_syntax, &ty)?;

        // Add the theorem to the environment
        if let Some(env) = &mut self.state_mut().env {
            add_definition(env, full_name.clone(), ty, Some(proof), vec![])?;

            // Add to exports if public
            self.state_mut().ns_ctx.add_export(full_name);
        }

        Ok(())
    }

    /// Elaborate axiom command
    fn elab_axiom(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        use crate::environment_ext::add_axiom;

        if node.children.len() < 2 {
            return Err(ElabError::InvalidSyntax(
                "Axiom requires name and type".to_string(),
            ));
        }

        // Parse the axiom name
        let name_syntax = &node.children[0];
        let axiom_name = self.parse_name(name_syntax)?;

        // Make the name absolute in the current namespace
        let full_name = Name::join_relative(self.state().ns_ctx.current_namespace(), &axiom_name);

        // Find the type (after :)
        let mut type_idx = None;
        for (i, child) in node.children.iter().enumerate() {
            if let Syntax::Atom(atom) = child {
                if atom.value.as_str() == ":" {
                    type_idx = Some(i + 1);
                    break;
                }
            }
        }

        let type_syntax = match type_idx {
            Some(idx) if idx < node.children.len() => &node.children[idx],
            _ => return Err(ElabError::InvalidSyntax("Axiom missing type".to_string())),
        };

        // Elaborate the type
        let ty = self.elaborate(type_syntax)?;

        // Add the axiom to the environment
        if let Some(env) = &mut self.state_mut().env {
            add_axiom(env, full_name.clone(), ty, vec![])?;

            // Add to exports if public
            self.state_mut().ns_ctx.add_export(full_name);
        }

        Ok(())
    }

    /// Elaborate constant command
    fn elab_constant(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        // Constants are basically axioms in Lean
        self.elab_axiom(node)
    }

    /// Elaborate variable command
    fn elab_variable(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<(), ElabError> {
        if node.children.is_empty() {
            return Err(ElabError::InvalidSyntax(
                "Variable requires at least one binder".to_string(),
            ));
        }

        // Variables are section-local and are automatically added to
        // definitions/theorems in the current section

        // Parse binders
        for child in &node.children {
            match child {
                Syntax::Node(binder_node) if self.is_binder_kind(binder_node.kind) => {
                    // Parse binder group: (x y : Type) or {α : Type u}
                    let (names, ty) = self.parse_binder_group(binder_node)?;

                    // Add each variable to the current section
                    for name in names {
                        self.state_mut().ns_ctx.add_section_variable(name)?;
                    }
                }
                _ => {
                    return Err(ElabError::InvalidSyntax(
                        "Invalid variable binder".to_string(),
                    ));
                }
            }
        }

        Ok(())
    }

    /// Check if a syntax kind represents a binder
    fn is_binder_kind(&self, kind: SyntaxKind) -> bool {
        // For now, accept any parenthesized or bracketed expression as a binder
        true
    }

    /// Parse a binder group into names and type
    fn parse_binder_group(
        &self,
        node: &lean_syn_expr::SyntaxNode,
    ) -> Result<(Vec<Name>, Expr), ElabError> {
        // TODO: Implement full binder parsing
        // For now, return a placeholder
        Ok((vec![Name::mk_simple("x")], Expr::sort(Level::zero())))
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

    /// Parse import options (only, hiding, renaming)
    fn parse_import_options(
        &self,
        node: &lean_syn_expr::SyntaxNode,
        module_name: Name,
    ) -> Result<Import, ElabError> {
        let mut import = Import::simple(module_name);
        
        // Look for import options in the syntax tree
        let mut i = 1; // Start after module name
        while i < node.children.len() {
            match &node.children[i] {
                Syntax::Atom(atom) => match atom.value.as_str() {
                    "only" => {
                        // Parse "only" list: import M only (x, y, z)
                        i += 1;
                        if i < node.children.len() {
                            import.only = Some(self.parse_name_list(&node.children[i])?);
                        }
                    }
                    "hiding" => {
                        // Parse "hiding" list: import M hiding (x, y, z)
                        i += 1;
                        if i < node.children.len() {
                            import.hiding = self.parse_name_list(&node.children[i])?;
                        }
                    }
                    "renaming" => {
                        // Parse "renaming" list: import M renaming (x → y, a → b)
                        i += 1;
                        if i < node.children.len() {
                            import.renaming = self.parse_renaming_list(&node.children[i])?;
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
            i += 1;
        }
        
        Ok(import)
    }
    
    /// Parse a list of names in parentheses
    fn parse_name_list(&self, syntax: &Syntax) -> Result<Vec<Name>, ElabError> {
        match syntax {
            Syntax::Node(node) => {
                let mut names = Vec::new();
                for child in &node.children {
                    match child {
                        Syntax::Atom(atom) if atom.value.as_str() != "," => {
                            names.push(Name::mk_simple(atom.value.as_str()));
                        }
                        Syntax::Node(_) => {
                            // Handle qualified names
                            names.push(self.parse_name(child)?);
                        }
                        _ => {}
                    }
                }
                Ok(names)
            }
            _ => Err(ElabError::InvalidSyntax(
                "Expected parenthesized list of names".to_string(),
            )),
        }
    }
    
    /// Parse a renaming list: (x → y, a → b)
    fn parse_renaming_list(&self, syntax: &Syntax) -> Result<HashMap<Name, Name>, ElabError> {
        match syntax {
            Syntax::Node(node) => {
                let mut renaming = HashMap::new();
                let mut i = 0;
                
                while i < node.children.len() {
                    // Parse "from" name
                    let from = self.parse_name(&node.children[i])?;
                    
                    // Skip arrow (→ or ->)
                    i += 1;
                    if i < node.children.len() {
                        if let Syntax::Atom(atom) = &node.children[i] {
                            if atom.value.as_str() == "→" || atom.value.as_str() == "->" {
                                i += 1;
                            }
                        }
                    }
                    
                    // Parse "to" name
                    if i < node.children.len() {
                        let to = self.parse_name(&node.children[i])?;
                        renaming.insert(from, to);
                        i += 1;
                        
                        // Skip comma
                        if i < node.children.len() {
                            if let Syntax::Atom(atom) = &node.children[i] {
                                if atom.value.as_str() == "," {
                                    i += 1;
                                }
                            }
                        }
                    } else {
                        return Err(ElabError::InvalidSyntax(
                            "Expected target name after arrow in renaming".to_string(),
                        ));
                    }
                }
                
                Ok(renaming)
            }
            _ => Err(ElabError::InvalidSyntax(
                "Expected parenthesized renaming list".to_string(),
            )),
        }
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
    use lean_parser::ExpandingParser;
    use std::path::PathBuf;
    use std::sync::Arc;
    use crate::module_loader::{ModuleLoader, ModuleLoaderConfig};

    #[test]
    fn test_import_elaboration() {
        let mut elaborator = Elaborator::new();
        elaborator.state_mut().set_env(init_basic_environment());

        // Create a simple import syntax
        let import_text = "import Std.Data.List";
        let mut parser = ExpandingParser::new(import_text);
        let module = parser.parse_module().expect("Failed to parse module");
        
        // Extract the first command from the module
        let syntax = match &module {
            Syntax::Node(node) if node.kind == SyntaxKind::Module => {
                node.children.first().expect("Module should have import command")
            }
            _ => panic!("Expected module syntax")
        };

        // The import should fail because the module doesn't exist
        let result = elaborator.elaborate_command(&syntax);
        assert!(result.is_err());
        
        match result {
            Err(ElabError::ModuleNotFound(name)) => {
                assert_eq!(name.to_string(), "Std.Data.List");
            }
            _ => panic!("Expected ModuleNotFound error"),
        }
    }

    #[test]
    fn test_import_with_module_loader_config() {
        // Create a module loader with custom search paths
        let mut config = ModuleLoaderConfig::default();
        config.search_paths.push(PathBuf::from("./test_modules"));
        
        let mut elaborator = Elaborator::new();
        // Replace the default module loader with our configured one
        elaborator.state_mut().module_loader = Arc::new(ModuleLoader::new(config));
        elaborator.state_mut().set_env(init_basic_environment());

        // Try to import a module that doesn't exist
        let import_text = "import TestModule";
        let mut parser = ExpandingParser::new(import_text);
        let module = parser.parse_module().expect("Failed to parse module");
        
        // Extract the first command from the module
        let syntax = match &module {
            Syntax::Node(node) if node.kind == SyntaxKind::Module => {
                node.children.first().expect("Module should have import command")
            }
            _ => panic!("Expected module syntax")
        };

        let result = elaborator.elaborate_command(&syntax);
        assert!(result.is_err());
    }

    #[test]
    fn test_import_options_parsing() {
        let elaborator = Elaborator::new();
        
        // Test parsing "only" option
        let import_node = lean_syn_expr::SyntaxNode::new(
            SyntaxKind::Import,
            lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
            smallvec![
                Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                    lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
                    eterned::BaseCoword::from("Std.Data.List")
                )),
                Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                    lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
                    eterned::BaseCoword::from("only")
                )),
                Syntax::Node(Box::new(lean_syn_expr::SyntaxNode::new(
                    SyntaxKind::App,
                    lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
                    smallvec![
                        Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                            lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
                            eterned::BaseCoword::from("map")
                        )),
                        Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                            lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
                            eterned::BaseCoword::from(",")
                        )),
                        Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                            lean_syn_expr::SourceRange {
                start: lean_syn_expr::SourcePos::new(0, 0, 0),
                end: lean_syn_expr::SourcePos::new(0, 0, 0),
            },
                            eterned::BaseCoword::from("filter")
                        )),
                    ]
                )))
            ],
        );
        
        let module_name = Name::mk_simple("Std.Data.List");
        let import = elaborator.parse_import_options(&import_node, module_name).unwrap();
        
        assert!(import.only.is_some());
        let only_list = import.only.unwrap();
        assert_eq!(only_list.len(), 2);
        assert_eq!(only_list[0], Name::mk_simple("map"));
        assert_eq!(only_list[1], Name::mk_simple("filter"));
    }

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
