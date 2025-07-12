//! Module representation and management
//!
//! This module defines the core data structures for Lean modules,
//! including module metadata, import relationships, and export lists.

use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use crate::Name;

/// Represents a Lean module
#[derive(Debug, Clone)]
pub struct Module {
    /// Module name (e.g., `Mathlib.Data.Nat.Basic`)
    pub name: Name,
    /// File path of the module
    pub path: PathBuf,
    /// List of imported modules
    pub imports: Vec<Import>,
    /// Exported names from this module
    pub exports: HashSet<Name>,
    /// Whether this is a prelude module (imported by default)
    pub is_prelude: bool,
    /// Module-level docstring
    pub doc: Option<String>,
}

/// Import declaration
#[derive(Debug, Clone)]
pub struct Import {
    /// Module being imported
    pub module: Name,
    /// Whether this is a runtime import (vs compile-time only)
    pub runtime: bool,
    /// Specific names to import (None means import all)
    pub only: Option<Vec<Name>>,
    /// Names to hide from the import
    pub hiding: Vec<Name>,
    /// Renaming map (from -> to)
    pub renaming: HashMap<Name, Name>,
}

/// Module visibility
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[derive(Default)]
pub enum Visibility {
    /// Public - visible to all importers
    #[default]
    Public,
    /// Protected - visible within the same namespace
    Protected,
    /// Private - visible only within the same module
    Private,
}

/// Module initialization state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleState {
    /// Not yet loaded
    Unloaded,
    /// Currently being loaded (for cycle detection)
    Loading,
    /// Parsed but not elaborated
    Parsed,
    /// Fully elaborated and type-checked
    Elaborated,
    /// Error during loading/elaboration
    Error,
}

/// Module metadata
#[derive(Debug, Clone)]
pub struct ModuleInfo {
    /// Module name
    pub name: Name,
    /// Module state
    pub state: ModuleState,
    /// File path
    pub path: PathBuf,
    /// Last modification time
    pub mtime: Option<std::time::SystemTime>,
    /// Dependencies (imported modules)
    pub dependencies: Vec<Name>,
    /// Reverse dependencies (modules that import this one)
    pub dependents: HashSet<Name>,
}

impl Module {
    /// Create a new module
    pub fn new(name: Name, path: PathBuf) -> Self {
        Self {
            name,
            path,
            imports: Vec::new(),
            exports: HashSet::new(),
            is_prelude: false,
            doc: None,
        }
    }

    /// Add an import to the module
    pub fn add_import(&mut self, import: Import) {
        self.imports.push(import);
    }

    /// Add an exported name
    pub fn add_export(&mut self, name: Name) {
        self.exports.insert(name);
    }

    /// Check if a name is exported
    pub fn is_exported(&self, name: &Name) -> bool {
        self.exports.contains(name)
    }

    /// Get all imported module names
    pub fn imported_modules(&self) -> Vec<&Name> {
        self.imports.iter().map(|i| &i.module).collect()
    }
}

impl Import {
    /// Create a simple import (import all)
    pub fn simple(module: Name) -> Self {
        Self {
            module,
            runtime: true,
            only: None,
            hiding: Vec::new(),
            renaming: HashMap::new(),
        }
    }

    /// Create a selective import
    pub fn selective(module: Name, names: Vec<Name>) -> Self {
        Self {
            module,
            runtime: true,
            only: Some(names),
            hiding: Vec::new(),
            renaming: HashMap::new(),
        }
    }

    /// Add a hiding clause
    pub fn with_hiding(mut self, names: Vec<Name>) -> Self {
        self.hiding = names;
        self
    }

    /// Add a renaming
    pub fn with_renaming(mut self, from: Name, to: Name) -> Self {
        self.renaming.insert(from, to);
        self
    }

    /// Check if a name is imported
    pub fn imports_name(&self, name: &Name) -> Option<Name> {
        // Check if hidden
        if self.hiding.iter().any(|n| n == name) {
            return None;
        }

        // Check if in only list (if specified)
        if let Some(only) = &self.only {
            if !only.iter().any(|n| n == name) {
                return None;
            }
        }

        // Apply renaming if exists
        if let Some(renamed) = self.renaming.get(name) {
            Some(renamed.clone())
        } else {
            Some(name.clone())
        }
    }
}


/// Module path resolution utilities
pub mod path {
    use std::path::Path;

    use super::*;

    /// Convert a module name to a file path
    pub fn module_name_to_path(name: &Name) -> PathBuf {
        let components = name.components();

        let mut path = PathBuf::new();
        for (i, component) in components.iter().enumerate() {
            if i == components.len() - 1 {
                path.push(format!("{component}.lean"));
            } else {
                path.push(component);
            }
        }
        path
    }

    /// Convert a file path to a module name
    pub fn path_to_module_name(path: &Path) -> Option<Name> {
        let path_str = path.to_str()?;

        // Remove .lean extension
        let without_ext = path_str.strip_suffix(".lean")?;

        // Split by path separator and join with dots
        let components: Vec<&str> = without_ext
            .split(std::path::MAIN_SEPARATOR)
            .filter(|s| !s.is_empty())
            .collect();

        if components.is_empty() {
            return None;
        }

        let mut name = Name::mk_simple(components[0]);
        for component in &components[1..] {
            name = Name::str(name, *component);
        }

        Some(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_creation() {
        let name = Name::mk_simple("Test");
        let path = PathBuf::from("Test.lean");
        let module = Module::new(name.clone(), path.clone());

        assert_eq!(module.name, name);
        assert_eq!(module.path, path);
        assert!(module.imports.is_empty());
        assert!(module.exports.is_empty());
    }

    #[test]
    fn test_import_simple() {
        let import = Import::simple(Name::mk_simple("Foo"));

        assert_eq!(import.module, Name::mk_simple("Foo"));
        assert!(import.runtime);
        assert!(import.only.is_none());
        assert!(import.hiding.is_empty());
        assert!(import.renaming.is_empty());
    }

    #[test]
    fn test_import_with_renaming() {
        let import = Import::simple(Name::mk_simple("Foo"))
            .with_renaming(Name::mk_simple("bar"), Name::mk_simple("baz"));

        assert_eq!(
            import.imports_name(&Name::mk_simple("bar")),
            Some(Name::mk_simple("baz"))
        );
        assert_eq!(
            import.imports_name(&Name::mk_simple("other")),
            Some(Name::mk_simple("other"))
        );
    }

    #[test]
    fn test_import_with_hiding() {
        let import =
            Import::simple(Name::mk_simple("Foo")).with_hiding(vec![Name::mk_simple("bar")]);

        assert_eq!(import.imports_name(&Name::mk_simple("bar")), None);
        assert_eq!(
            import.imports_name(&Name::mk_simple("baz")),
            Some(Name::mk_simple("baz"))
        );
    }

    #[test]
    fn test_module_name_to_path() {
        let name = Name::str(Name::str(Name::mk_simple("Mathlib"), "Data"), "Nat");
        let path = path::module_name_to_path(&name);

        // Use platform-independent path construction for comparison
        let expected = PathBuf::from("Mathlib").join("Data").join("Nat.lean");
        assert_eq!(path, expected);
    }

    #[test]
    fn test_path_to_module_name() {
        // Use PathBuf::from to create a platform-independent path
        let path = PathBuf::from("Mathlib").join("Data").join("Nat.lean");
        let name = path::path_to_module_name(&path).unwrap();

        let expected = Name::str(Name::str(Name::mk_simple("Mathlib"), "Data"), "Nat");
        assert_eq!(name, expected);
    }
}
