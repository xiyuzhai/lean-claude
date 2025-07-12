use std::collections::HashSet;

use indexmap::IndexMap;

use crate::{expr::Expr, name::Name};

#[derive(Debug, Clone)]
pub struct Environment {
    declarations: IndexMap<Name, Declaration>,
    universe_names: HashSet<Name>,
}

#[derive(Debug, Clone)]
pub struct Declaration {
    pub name: Name,
    pub universe_params: Vec<Name>,
    pub ty: Expr,
    pub value: Option<Expr>,
    pub is_trusted: bool,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            declarations: IndexMap::new(),
            universe_names: HashSet::new(),
        }
    }

    pub fn add_universe(&mut self, name: Name) -> Result<(), String> {
        if self.universe_names.contains(&name) {
            return Err(format!("universe '{name}' already declared"));
        }
        self.universe_names.insert(name);
        Ok(())
    }

    pub fn add_declaration(&mut self, decl: Declaration) -> Result<(), String> {
        if self.declarations.contains_key(&decl.name) {
            return Err(format!("declaration '{}' already exists", decl.name));
        }

        // Verify universe parameters are declared
        for univ in &decl.universe_params {
            if !self.universe_names.contains(univ) {
                return Err(format!("universe '{univ}' not declared"));
            }
        }

        self.declarations.insert(decl.name.clone(), decl);
        Ok(())
    }

    /// Add a declaration with a specific name (for imports with renaming)
    pub fn add_declaration_with_name(
        &mut self,
        name: Name,
        decl: Declaration,
    ) -> Result<(), String> {
        if self.declarations.contains_key(&name) {
            return Err(format!("declaration '{}' already exists", name));
        }

        // Verify universe parameters are declared
        for univ in &decl.universe_params {
            if !self.universe_names.contains(univ) {
                return Err(format!("universe '{univ}' not declared"));
            }
        }

        self.declarations.insert(name, decl);
        Ok(())
    }

    pub fn get_declaration(&self, name: &Name) -> Option<&Declaration> {
        self.declarations.get(name)
    }

    pub fn contains(&self, name: &Name) -> bool {
        self.declarations.contains_key(name)
    }

    pub fn universe_names(&self) -> &HashSet<Name> {
        &self.universe_names
    }

    pub fn declarations(&self) -> impl Iterator<Item = &Declaration> {
        self.declarations.values()
    }

    /// Get all declarations as a vector of (name, declaration) pairs
    pub fn get_all_declarations(&self) -> Vec<(&Name, &Declaration)> {
        self.declarations.iter().collect()
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}
