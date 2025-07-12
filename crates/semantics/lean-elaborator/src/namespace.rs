//! Namespace management and name resolution
//!
//! This module handles namespace scoping, name resolution,
//! and the implementation of the `open` command.

use std::collections::{HashMap, HashSet};

use lean_kernel::{module::Visibility, Name};

use crate::error::ElabError;

/// Namespace context for name resolution
#[derive(Debug, Clone)]
pub struct NamespaceContext {
    /// Stack of namespace scopes (innermost last)
    namespace_stack: Vec<Name>,
    /// Currently opened namespaces
    opened_namespaces: Vec<OpenedNamespace>,
    /// Namespace aliases (alias -> full namespace)
    namespace_aliases: HashMap<Name, Name>,
    /// Section variables (for local scoping)
    section_vars: Vec<SectionScope>,
    /// Exported names from the current module
    exports: HashSet<Name>,
}

/// An opened namespace with its options
#[derive(Debug, Clone)]
pub struct OpenedNamespace {
    /// The namespace that was opened
    pub namespace: Name,
    /// Specific names to import (None means all)
    pub only: Option<HashSet<Name>>,
    /// Names to hide
    pub hiding: HashSet<Name>,
    /// Renaming map (from -> to)
    pub renaming: HashMap<Name, Name>,
}

/// Section scope for local variables
#[derive(Debug, Clone)]
pub struct SectionScope {
    /// Section name (if any)
    pub name: Option<Name>,
    /// Variables defined in this section
    pub variables: Vec<Name>,
    /// Universe parameters in this section
    pub universes: Vec<Name>,
}

impl NamespaceContext {
    /// Create a new empty namespace context
    pub fn new() -> Self {
        Self {
            namespace_stack: vec![Name::anonymous()], // Start in root namespace
            opened_namespaces: Vec::new(),
            namespace_aliases: HashMap::new(),
            section_vars: Vec::new(),
            exports: HashSet::new(),
        }
    }

    /// Get the current namespace
    pub fn current_namespace(&self) -> &Name {
        self.namespace_stack.last().unwrap()
    }

    /// Push a new namespace onto the stack
    pub fn push_namespace(&mut self, name: Name) {
        let current = self.current_namespace().clone();
        let full_name = if current.is_anonymous() {
            name
        } else {
            Name::join_relative(&current, &name)
        };
        self.namespace_stack.push(full_name);
    }

    /// Pop a namespace from the stack
    pub fn pop_namespace(&mut self) -> Result<Name, ElabError> {
        if self.namespace_stack.len() <= 1 {
            return Err(ElabError::ElaborationFailed(
                "Cannot pop root namespace".to_string(),
            ));
        }
        Ok(self.namespace_stack.pop().unwrap())
    }

    /// Open a namespace
    pub fn open_namespace(&mut self, ns: OpenedNamespace) {
        self.opened_namespaces.push(ns);
    }

    /// Add a namespace alias
    pub fn add_alias(&mut self, alias: Name, target: Name) {
        self.namespace_aliases.insert(alias, target);
    }

    /// Resolve a name in the current context
    pub fn resolve_name(&self, name: &Name) -> Vec<ResolvedName> {
        let mut results = Vec::new();

        // If it's already fully qualified, return as-is
        if self.is_fully_qualified(name) {
            results.push(ResolvedName {
                name: name.clone(),
                source: NameSource::Explicit,
                visibility: Visibility::Public,
            });
            return results;
        }

        // Try current namespace
        let current_ns = self.current_namespace();
        if !current_ns.is_anonymous() {
            let qualified = Name::join_relative(current_ns, name);
            results.push(ResolvedName {
                name: qualified,
                source: NameSource::CurrentNamespace,
                visibility: Visibility::Public,
            });
        }

        // Try opened namespaces
        for opened in self.opened_namespaces.iter().rev() {
            if let Some(resolved) = self.resolve_in_opened(name, opened) {
                results.push(resolved);
            }
        }

        // Try namespace aliases
        if let Some(expanded) = self.expand_alias(name) {
            results.push(ResolvedName {
                name: expanded,
                source: NameSource::Alias,
                visibility: Visibility::Public,
            });
        }

        // Try root namespace
        results.push(ResolvedName {
            name: name.clone(),
            source: NameSource::Root,
            visibility: Visibility::Public,
        });

        results
    }

    /// Resolve a name within an opened namespace
    fn resolve_in_opened(&self, name: &Name, opened: &OpenedNamespace) -> Option<ResolvedName> {
        // Check if hidden
        if opened.hiding.contains(name) {
            return None;
        }

        // Check if in only list (if specified)
        if let Some(only) = &opened.only {
            if !only.contains(name) {
                return None;
            }
        }

        // Apply renaming if exists
        let resolved_name = if let Some(renamed) = opened.renaming.get(name) {
            renamed.clone()
        } else {
            Name::join_relative(&opened.namespace, name)
        };

        Some(ResolvedName {
            name: resolved_name,
            source: NameSource::OpenedNamespace(opened.namespace.clone()),
            visibility: Visibility::Public,
        })
    }

    /// Expand namespace aliases in a name
    fn expand_alias(&self, name: &Name) -> Option<Name> {
        // Get the root component
        let components = name.components();
        if components.is_empty() {
            return None;
        }

        let root = Name::mk_simple(components[0].to_string());

        // Check if it's an alias
        if let Some(expanded) = self.namespace_aliases.get(&root) {
            // Rebuild with expanded root
            let mut result = expanded.clone();
            for component in &components[1..] {
                result = Name::str(result, component.to_string());
            }
            Some(result)
        } else {
            None
        }
    }

    /// Check if a name is fully qualified
    fn is_fully_qualified(&self, _name: &Name) -> bool {
        // In Lean, names starting with certain prefixes are considered fully qualified
        // For now, we'll assume all multi-component names might be fully qualified
        false
    }

    /// Enter a section
    pub fn enter_section(&mut self, name: Option<Name>) {
        self.section_vars.push(SectionScope {
            name,
            variables: Vec::new(),
            universes: Vec::new(),
        });
    }

    /// Exit a section
    pub fn exit_section(&mut self) -> Result<SectionScope, ElabError> {
        self.section_vars
            .pop()
            .ok_or_else(|| ElabError::ElaborationFailed("No section to exit".to_string()))
    }

    /// Add a section variable
    pub fn add_section_variable(&mut self, name: Name) -> Result<(), ElabError> {
        if let Some(section) = self.section_vars.last_mut() {
            section.variables.push(name);
            Ok(())
        } else {
            Err(ElabError::ElaborationFailed(
                "No active section for variable".to_string(),
            ))
        }
    }

    /// Add a section universe parameter
    pub fn add_section_universe(&mut self, name: Name) -> Result<(), ElabError> {
        if let Some(section) = self.section_vars.last_mut() {
            section.universes.push(name);
            Ok(())
        } else {
            Err(ElabError::ElaborationFailed(
                "No active section for universe".to_string(),
            ))
        }
    }

    /// Get all section variables in scope
    pub fn section_variables(&self) -> Vec<&Name> {
        self.section_vars
            .iter()
            .flat_map(|s| s.variables.iter())
            .collect()
    }

    /// Get all section universe parameters in scope
    pub fn section_universes(&self) -> Vec<&Name> {
        self.section_vars
            .iter()
            .flat_map(|s| s.universes.iter())
            .collect()
    }

    /// Add an exported name
    pub fn add_export(&mut self, name: Name) {
        self.exports.insert(name);
    }

    /// Get all exported names
    pub fn exports(&self) -> &HashSet<Name> {
        &self.exports
    }
}

/// A resolved name with its source information
#[derive(Debug, Clone)]
pub struct ResolvedName {
    /// The fully qualified name
    pub name: Name,
    /// Where the name was resolved from
    pub source: NameSource,
    /// Visibility of the name
    pub visibility: Visibility,
}

/// Source of a resolved name
#[derive(Debug, Clone)]
pub enum NameSource {
    /// Explicitly qualified name
    Explicit,
    /// Resolved from current namespace
    CurrentNamespace,
    /// Resolved from an opened namespace
    OpenedNamespace(Name),
    /// Resolved via namespace alias
    Alias,
    /// Resolved from root namespace
    Root,
}

impl Default for NamespaceContext {
    fn default() -> Self {
        Self::new()
    }
}

impl OpenedNamespace {
    /// Create a simple open (open all)
    pub fn new(namespace: Name) -> Self {
        Self {
            namespace,
            only: None,
            hiding: HashSet::new(),
            renaming: HashMap::new(),
        }
    }

    /// Create a selective open
    pub fn selective(namespace: Name, names: Vec<Name>) -> Self {
        Self {
            namespace,
            only: Some(names.into_iter().collect()),
            hiding: HashSet::new(),
            renaming: HashMap::new(),
        }
    }

    /// Add names to hide
    pub fn with_hiding(mut self, names: Vec<Name>) -> Self {
        self.hiding = names.into_iter().collect();
        self
    }

    /// Add a renaming
    pub fn with_renaming(mut self, from: Name, to: Name) -> Self {
        self.renaming.insert(from, to);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_namespace_stack() {
        let mut ctx = NamespaceContext::new();

        assert_eq!(ctx.current_namespace(), &Name::anonymous());

        ctx.push_namespace(Name::mk_simple("Foo"));
        assert_eq!(ctx.current_namespace(), &Name::mk_simple("Foo"));

        ctx.push_namespace(Name::mk_simple("Bar"));
        assert_eq!(
            ctx.current_namespace(),
            &Name::str(Name::mk_simple("Foo"), "Bar")
        );

        ctx.pop_namespace().unwrap();
        assert_eq!(ctx.current_namespace(), &Name::mk_simple("Foo"));
    }

    #[test]
    fn test_name_resolution_current_namespace() {
        let mut ctx = NamespaceContext::new();
        ctx.push_namespace(Name::mk_simple("Foo"));

        let resolved = ctx.resolve_name(&Name::mk_simple("bar"));

        assert!(resolved.iter().any(|r| {
            r.name == Name::str(Name::mk_simple("Foo"), "bar")
                && matches!(r.source, NameSource::CurrentNamespace)
        }));
    }

    #[test]
    fn test_open_namespace() {
        let mut ctx = NamespaceContext::new();

        let opened = OpenedNamespace::new(Name::mk_simple("Std"));
        ctx.open_namespace(opened);

        let resolved = ctx.resolve_name(&Name::mk_simple("List"));

        assert!(resolved.iter().any(|r| {
            r.name == Name::str(Name::mk_simple("Std"), "List")
                && matches!(r.source, NameSource::OpenedNamespace(_))
        }));
    }

    #[test]
    fn test_namespace_alias() {
        let mut ctx = NamespaceContext::new();

        ctx.add_alias(
            Name::mk_simple("M"),
            Name::str(Name::mk_simple("Mathlib"), "Data"),
        );

        let name = Name::str(Name::mk_simple("M"), "Nat");
        let resolved = ctx.resolve_name(&name);

        assert!(resolved.iter().any(|r| {
            r.name == Name::str(Name::str(Name::mk_simple("Mathlib"), "Data"), "Nat")
                && matches!(r.source, NameSource::Alias)
        }));
    }

    #[test]
    fn test_selective_open() {
        let mut ctx = NamespaceContext::new();

        let opened = OpenedNamespace::selective(
            Name::mk_simple("Foo"),
            vec![Name::mk_simple("bar"), Name::mk_simple("baz")],
        );
        ctx.open_namespace(opened);

        let bar_resolved = ctx.resolve_name(&Name::mk_simple("bar"));
        let qux_resolved = ctx.resolve_name(&Name::mk_simple("qux"));

        // bar should be found in Foo
        assert!(bar_resolved
            .iter()
            .any(|r| { r.name == Name::str(Name::mk_simple("Foo"), "bar") }));

        // qux should not be found in Foo (not in only list)
        assert!(!qux_resolved.iter().any(|r| {
            r.name == Name::str(Name::mk_simple("Foo"), "qux")
                && matches!(r.source, NameSource::OpenedNamespace(_))
        }));
    }

    #[test]
    fn test_section_variables() {
        let mut ctx = NamespaceContext::new();

        ctx.enter_section(Some(Name::mk_simple("test")));
        ctx.add_section_variable(Name::mk_simple("x")).unwrap();
        ctx.add_section_universe(Name::mk_simple("u")).unwrap();

        assert_eq!(ctx.section_variables().len(), 1);
        assert_eq!(ctx.section_universes().len(), 1);

        let section = ctx.exit_section().unwrap();
        assert_eq!(section.name, Some(Name::mk_simple("test")));
        assert_eq!(section.variables.len(), 1);
        assert_eq!(section.universes.len(), 1);
    }
}
