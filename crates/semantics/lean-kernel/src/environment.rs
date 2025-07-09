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
            return Err(format!("universe '{}' already declared", name));
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
                return Err(format!("universe '{}' not declared", univ));
            }
        }

        self.declarations.insert(decl.name.clone(), decl);
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
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}
