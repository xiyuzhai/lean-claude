//! Module loading and dependency management
//!
//! This module handles finding, loading, and caching Lean modules,
//! as well as managing module dependencies.

use std::{
    collections::{HashMap, HashSet, VecDeque},
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
};

use lean_kernel::{
    environment::{Declaration, Environment},
    module::{Import, Module, ModuleInfo, ModuleState},
    Name,
};
use lean_parser::ExpandingParser;
use lean_syn_expr::{Syntax, SyntaxKind};

use crate::{error::ElabError, ElabState, Elaborator};

/// Module loader configuration
#[derive(Debug, Clone)]
pub struct ModuleLoaderConfig {
    /// Search paths for modules
    pub search_paths: Vec<PathBuf>,
    /// Path to the Lean standard library
    pub lean_path: Option<PathBuf>,
    /// Whether to use module cache
    pub use_cache: bool,
    /// Maximum depth for import resolution
    pub max_import_depth: usize,
}

/// Module loader for finding and loading Lean modules
pub struct ModuleLoader {
    /// Configuration
    config: ModuleLoaderConfig,
    /// Module cache
    cache: Arc<Mutex<ModuleCache>>,
    /// Module dependency graph
    dependencies: Arc<Mutex<DependencyGraph>>,
}

/// Module cache
struct ModuleCache {
    /// Parsed modules
    parsed: HashMap<Name, (Module, Syntax)>,
    /// Elaborated modules  
    elaborated: HashMap<Name, Arc<Environment>>,
    /// Module info
    info: HashMap<Name, ModuleInfo>,
}

/// Module dependency graph
struct DependencyGraph {
    /// Forward dependencies (module -> modules it imports)
    forward: HashMap<Name, HashSet<Name>>,
    /// Reverse dependencies (module -> modules that import it)
    reverse: HashMap<Name, HashSet<Name>>,
    /// Modules currently being loaded (for cycle detection)
    loading: HashSet<Name>,
}

impl ModuleLoader {
    /// Create a new module loader
    pub fn new(config: ModuleLoaderConfig) -> Self {
        Self {
            config,
            cache: Arc::new(Mutex::new(ModuleCache::new())),
            dependencies: Arc::new(Mutex::new(DependencyGraph::new())),
        }
    }

    /// Find a module file
    pub fn find_module(&self, name: &Name) -> Result<PathBuf, ElabError> {
        let relative_path = lean_kernel::module::path::module_name_to_path(name);

        // Try each search path
        for search_path in &self.config.search_paths {
            let full_path = search_path.join(&relative_path);
            if full_path.exists() {
                return Ok(full_path);
            }
        }

        // Try Lean standard library path
        if let Some(lean_path) = &self.config.lean_path {
            let full_path = lean_path.join(&relative_path);
            if full_path.exists() {
                return Ok(full_path);
            }
        }

        Err(ElabError::ModuleNotFound(name.clone()))
    }

    /// Load a module (parse only)
    pub fn load_module(&self, name: &Name) -> Result<(Module, Syntax), ElabError> {
        // Check cache first
        if self.config.use_cache {
            let cache = self.cache.lock().unwrap();
            if let Some(cached) = cache.parsed.get(name) {
                return Ok(cached.clone());
            }
        }

        // Check for import cycles
        {
            let mut deps = self.dependencies.lock().unwrap();
            if deps.loading.contains(name) {
                return Err(ElabError::ImportCycle(name.clone()));
            }
            deps.loading.insert(name.clone());
        }

        // Find and load the module file
        let path = self.find_module(name)?;
        let content =
            std::fs::read_to_string(&path).map_err(|e| ElabError::IOError(e.to_string()))?;

        // Parse the module
        let mut parser = ExpandingParser::new(&content);
        let syntax = parser
            .parse_module()
            .map_err(|e| ElabError::ParseError(e.to_string()))?;

        // Create module structure
        let mut module = Module::new(name.clone(), path);

        // Extract imports from syntax
        self.extract_imports(&syntax, &mut module)?;

        // Update cache
        if self.config.use_cache {
            let mut cache = self.cache.lock().unwrap();
            cache
                .parsed
                .insert(name.clone(), (module.clone(), syntax.clone()));

            let info = ModuleInfo {
                name: name.clone(),
                state: ModuleState::Parsed,
                path: module.path.clone(),
                mtime: std::fs::metadata(&module.path)
                    .ok()
                    .and_then(|m| m.modified().ok()),
                dependencies: module.imported_modules().into_iter().cloned().collect(),
                dependents: HashSet::new(),
            };
            cache.info.insert(name.clone(), info);
        }

        // Update dependency graph
        {
            let mut deps = self.dependencies.lock().unwrap();
            deps.loading.remove(name);

            let imported: HashSet<Name> = module.imported_modules().into_iter().cloned().collect();
            deps.forward.insert(name.clone(), imported.clone());

            // Update reverse dependencies
            for imported_name in imported {
                deps.reverse
                    .entry(imported_name)
                    .or_insert_with(HashSet::new)
                    .insert(name.clone());
            }
        }

        Ok((module, syntax))
    }

    /// Elaborate a module with all its dependencies
    pub fn elaborate_module(
        &self,
        name: &Name,
        base_env: Environment,
    ) -> Result<Arc<Environment>, ElabError> {
        // Check cache first
        if self.config.use_cache {
            let cache = self.cache.lock().unwrap();
            if let Some(env) = cache.elaborated.get(name) {
                return Ok(env.clone());
            }
        }

        // Load the module
        let (module, syntax) = self.load_module(name)?;

        // Create environment with imported modules
        let mut env = base_env;

        // Load and merge all imported modules first
        for import in &module.imports {
            let imported_env = self.elaborate_module(&import.module, env.clone())?;
            // TODO: Merge imported environment based on import options
            env = self.merge_environments(env, &imported_env, &import)?;
        }

        // Elaborate this module's content
        let mut elaborator = Elaborator::new();
        elaborator.state_mut().set_env(env.clone());

        // Elaborate the module syntax
        self.elaborate_module_syntax(&mut elaborator, &syntax)?;

        // Get the final environment
        let final_env = Arc::new(elaborator.state().env.clone().unwrap_or(env));

        // Update cache
        if self.config.use_cache {
            let mut cache = self.cache.lock().unwrap();
            cache.elaborated.insert(name.clone(), final_env.clone());

            if let Some(info) = cache.info.get_mut(name) {
                info.state = ModuleState::Elaborated;
            }
        }

        Ok(final_env)
    }

    /// Extract imports from module syntax
    fn extract_imports(&self, syntax: &Syntax, module: &mut Module) -> Result<(), ElabError> {
        match syntax {
            Syntax::Node(node) if node.kind == SyntaxKind::Module => {
                // Walk through top-level commands
                for child in &node.children {
                    if let Syntax::Node(cmd_node) = child {
                        if cmd_node.kind == SyntaxKind::Import {
                            // Extract import information
                            if let Some(module_name) = self.extract_import_module_name(cmd_node) {
                                // For now, create a simple import
                                // TODO: Extract import options (only, hiding, renaming)
                                let import = Import::simple(module_name);
                                module.imports.push(import);
                            }
                        }
                    }
                }
            }
            _ => {}
        }

        Ok(())
    }

    /// Extract module name from import syntax
    fn extract_import_module_name(&self, import_node: &lean_syn_expr::SyntaxNode) -> Option<Name> {
        // Import syntax should have at least one child with the module name
        if let Some(first_child) = import_node.children.first() {
            match first_child {
                Syntax::Atom(atom) => Some(Name::mk_simple(atom.value.as_str())),
                Syntax::Node(node) if node.kind == SyntaxKind::Identifier => {
                    // Handle qualified names
                    self.extract_qualified_name(node)
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Extract a qualified name from identifier node
    fn extract_qualified_name(&self, node: &lean_syn_expr::SyntaxNode) -> Option<Name> {
        // For now, just take the first atom
        // TODO: Properly handle qualified names like Foo.Bar.Baz
        if let Some(Syntax::Atom(atom)) = node.children.first() {
            Some(Name::mk_simple(atom.value.as_str()))
        } else {
            None
        }
    }

    /// Elaborate module syntax
    fn elaborate_module_syntax(
        &self,
        elaborator: &mut Elaborator,
        syntax: &Syntax,
    ) -> Result<(), ElabError> {
        crate::command::elaborate_module_commands(elaborator, syntax)
    }

    /// Merge environments based on import options
    pub fn merge_environments(
        &self,
        mut base: Environment,
        imported: &Environment,
        import: &lean_kernel::module::Import,
    ) -> Result<Environment, ElabError> {
        // Get all declarations from the imported environment
        let imported_decls = imported.get_all_declarations();

        // Filter based on import options
        for (name, decl) in imported_decls {
            // Check if this declaration should be imported
            if self.should_import_declaration(&name, &import) {
                // Apply renaming if needed
                let imported_name = if let Some(renamed) = import.renaming.get(&name) {
                    renamed.clone()
                } else {
                    name.clone()
                };

                // Add to base environment
                if imported_name != *name {
                    // Need to create a new declaration with the renamed name
                    let mut renamed_decl = decl.clone();
                    renamed_decl.name = imported_name;
                    base.add_declaration(renamed_decl)
                        .map_err(|e| ElabError::ElaborationFailed(e.to_string()))?;
                } else {
                    base.add_declaration(decl.clone())
                        .map_err(|e| ElabError::ElaborationFailed(e.to_string()))?;
                }
            }
        }

        Ok(base)
    }

    /// Check if a declaration should be imported based on import options
    fn should_import_declaration(&self, name: &Name, import: &Import) -> bool {
        // Check 'only' list
        if let Some(only) = &import.only {
            if !only.contains(name) {
                return false;
            }
        }

        // Check 'hiding' list
        if import.hiding.contains(name) {
            return false;
        }

        true
    }

    /// Get all transitive dependencies of a module
    pub fn get_dependencies(&self, name: &Name) -> Result<Vec<Name>, ElabError> {
        let deps = self.dependencies.lock().unwrap();
        let mut visited = HashSet::new();
        let mut result = Vec::new();
        let mut queue = VecDeque::new();

        queue.push_back(name.clone());

        while let Some(current) = queue.pop_front() {
            if visited.insert(current.clone()) {
                if let Some(forward_deps) = deps.forward.get(&current) {
                    for dep in forward_deps {
                        if !visited.contains(dep) {
                            queue.push_back(dep.clone());
                            result.push(dep.clone());
                        }
                    }
                }
            }
        }

        Ok(result)
    }

    /// Check if there's a dependency path from `from` to `to`
    pub fn has_dependency_path(&self, from: &Name, to: &Name) -> bool {
        let deps = self.dependencies.lock().unwrap();
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        queue.push_back(from.clone());

        while let Some(current) = queue.pop_front() {
            if &current == to {
                return true;
            }

            if visited.insert(current.clone()) {
                if let Some(forward_deps) = deps.forward.get(&current) {
                    for dep in forward_deps {
                        if !visited.contains(dep) {
                            queue.push_back(dep.clone());
                        }
                    }
                }
            }
        }

        false
    }

    /// Clear the module cache
    pub fn clear_cache(&self) {
        let mut cache = self.cache.lock().unwrap();
        cache.parsed.clear();
        cache.elaborated.clear();
        cache.info.clear();

        let mut deps = self.dependencies.lock().unwrap();
        deps.forward.clear();
        deps.reverse.clear();
        deps.loading.clear();
    }
}

impl ModuleCache {
    fn new() -> Self {
        Self {
            parsed: HashMap::new(),
            elaborated: HashMap::new(),
            info: HashMap::new(),
        }
    }
}

impl DependencyGraph {
    fn new() -> Self {
        Self {
            forward: HashMap::new(),
            reverse: HashMap::new(),
            loading: HashSet::new(),
        }
    }
}

impl Default for ModuleLoaderConfig {
    fn default() -> Self {
        Self {
            search_paths: vec![PathBuf::from(".")],
            lean_path: None,
            use_cache: true,
            max_import_depth: 100,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_loader_creation() {
        let config = ModuleLoaderConfig::default();
        let _loader = ModuleLoader::new(config);
    }

    #[test]
    fn test_dependency_graph() {
        let mut graph = DependencyGraph::new();

        let a = Name::mk_simple("A");
        let b = Name::mk_simple("B");
        let c = Name::mk_simple("C");

        graph
            .forward
            .insert(a.clone(), [b.clone()].into_iter().collect());
        graph
            .forward
            .insert(b.clone(), [c.clone()].into_iter().collect());

        // Check forward dependencies
        assert!(graph.forward[&a].contains(&b));
        assert!(graph.forward[&b].contains(&c));
    }

    #[test]
    fn test_cycle_detection() {
        let config = ModuleLoaderConfig::default();
        let loader = ModuleLoader::new(config);

        // Simulate loading a module
        let name = Name::mk_simple("Test");
        {
            let mut deps = loader.dependencies.lock().unwrap();
            deps.loading.insert(name.clone());
        }

        // Try to load the same module again (should detect cycle)
        let result = loader.load_module(&name);
        assert!(matches!(result, Err(ElabError::ImportCycle(_))));
    }
}
