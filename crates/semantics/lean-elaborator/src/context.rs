//! Local context management for the elaborator
//!
//! The local context tracks:
//! - Local variables (fvars) with their types
//! - Local definitions (let bindings)
//! - Universe level parameters
//! - Metavariable assignments

use std::collections::HashMap;

use lean_kernel::{Expr, Name};

/// Local declaration in the context
#[derive(Debug, Clone)]
pub enum LocalDecl {
    /// A local variable declaration (from lambda or forall binders)
    LocalDecl {
        name: Name,
        ty: Expr,
        /// Unique identifier for this variable
        fvar_id: Name,
    },
    /// A local definition (from let bindings)
    LocalDef {
        name: Name,
        ty: Option<Expr>,
        value: Expr,
        /// Unique identifier for this variable
        fvar_id: Name,
    },
}

/// Local context for elaboration
#[derive(Debug, Clone, Default)]
pub struct LocalContext {
    /// Map from fvar names to their declarations
    decls: HashMap<Name, LocalDecl>,
    /// Stack of fvar names in declaration order
    /// This is important for correct De Bruijn index calculation
    fvar_stack: Vec<Name>,
    /// Counter for generating unique fvar names
    next_fvar_id: u64,
}

impl LocalContext {
    pub fn new() -> Self {
        Self::default()
    }

    /// Push a new local declaration
    pub fn push_local_decl(&mut self, name: Name, ty: Expr) -> Name {
        let fvar_id = self.gen_fresh_fvar_name();
        let decl = LocalDecl::LocalDecl {
            name: name.clone(),
            ty,
            fvar_id: fvar_id.clone(),
        };
        self.decls.insert(fvar_id.clone(), decl);
        self.fvar_stack.push(fvar_id.clone());
        fvar_id
    }

    /// Push a new local definition
    pub fn push_local_def(&mut self, name: Name, ty: Option<Expr>, value: Expr) -> Name {
        let fvar_id = self.gen_fresh_fvar_name();
        let decl = LocalDecl::LocalDef {
            name: name.clone(),
            ty,
            value,
            fvar_id: fvar_id.clone(),
        };
        self.decls.insert(fvar_id.clone(), decl);
        self.fvar_stack.push(fvar_id.clone());
        fvar_id
    }

    /// Pop the most recent local declaration
    pub fn pop(&mut self) -> Option<Name> {
        if let Some(fvar_id) = self.fvar_stack.pop() {
            self.decls.remove(&fvar_id);
            Some(fvar_id)
        } else {
            None
        }
    }

    /// Get a local declaration by fvar name
    pub fn get(&self, fvar_id: &Name) -> Option<&LocalDecl> {
        self.decls.get(fvar_id)
    }

    /// Get the type of a local declaration
    pub fn get_type(&self, fvar_id: &Name) -> Option<&Expr> {
        match self.decls.get(fvar_id)? {
            LocalDecl::LocalDecl { ty, .. } => Some(ty),
            LocalDecl::LocalDef { ty, .. } => ty.as_ref(),
        }
    }

    /// Get the value of a local definition
    pub fn get_value(&self, fvar_id: &Name) -> Option<&Expr> {
        match self.decls.get(fvar_id)? {
            LocalDecl::LocalDecl { .. } => None,
            LocalDecl::LocalDef { value, .. } => Some(value),
        }
    }

    /// Find a local declaration by user-facing name
    pub fn find_by_user_name(&self, name: &Name) -> Option<&Name> {
        // Search from the end (most recent bindings first)
        for fvar_id in self.fvar_stack.iter().rev() {
            if let Some(decl) = self.decls.get(fvar_id) {
                let decl_name = match decl {
                    LocalDecl::LocalDecl { name, .. } => name,
                    LocalDecl::LocalDef { name, .. } => name,
                };
                if decl_name == name {
                    return Some(fvar_id);
                }
            }
        }
        None
    }

    /// Calculate the De Bruijn index for an fvar
    /// Returns None if the fvar is not in the context
    pub fn fvar_to_bvar(&self, fvar_id: &Name) -> Option<u32> {
        let pos = self.fvar_stack.iter().rposition(|id| id == fvar_id)?;
        Some((self.fvar_stack.len() - pos - 1) as u32)
    }

    /// Get the current depth (number of local declarations)
    pub fn depth(&self) -> usize {
        self.fvar_stack.len()
    }

    /// Generate a fresh fvar name
    fn gen_fresh_fvar_name(&mut self) -> Name {
        let id = self.next_fvar_id;
        self.next_fvar_id += 1;
        Name::mk_simple(format!("_fvar.{id}"))
    }

    /// Create a scope for temporary declarations
    pub fn with_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let depth = self.fvar_stack.len();
        let result = f(self);
        // Pop all declarations added in the scope
        while self.fvar_stack.len() > depth {
            self.pop();
        }
        result
    }
}

/// Universe level context
#[derive(Debug, Clone, Default)]
pub struct LevelContext {
    /// Set of universe parameters in scope
    params: Vec<Name>,
}

impl LevelContext {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a universe parameter
    pub fn add_param(&mut self, name: Name) {
        if !self.params.contains(&name) {
            self.params.push(name);
        }
    }

    /// Check if a name is a universe parameter
    pub fn is_param(&self, name: &Name) -> bool {
        self.params.contains(name)
    }

    /// Get all universe parameters
    pub fn params(&self) -> &[Name] {
        &self.params
    }
}

#[cfg(test)]
mod tests {
    use lean_kernel::{expr::ExprKind, Level};

    use super::*;

    #[test]
    fn test_local_context_basic() {
        let mut ctx = LocalContext::new();

        // Add a local declaration
        let x_ty = Expr {
            kind: ExprKind::Sort(Level::zero()),
        };
        let x_fvar = ctx.push_local_decl(Name::mk_simple("x"), x_ty.clone());

        // Check we can retrieve it
        assert!(ctx.get(&x_fvar).is_some());
        assert_eq!(ctx.get_type(&x_fvar), Some(&x_ty));

        // Check De Bruijn index
        assert_eq!(ctx.fvar_to_bvar(&x_fvar), Some(0));

        // Add another declaration
        let y_fvar = ctx.push_local_decl(Name::mk_simple("y"), x_ty.clone());
        assert_eq!(ctx.fvar_to_bvar(&x_fvar), Some(1));
        assert_eq!(ctx.fvar_to_bvar(&y_fvar), Some(0));

        // Pop and check
        ctx.pop();
        assert!(ctx.get(&y_fvar).is_none());
        assert_eq!(ctx.fvar_to_bvar(&x_fvar), Some(0));
    }

    #[test]
    fn test_local_context_scope() {
        let mut ctx = LocalContext::new();

        let x_ty = Expr {
            kind: ExprKind::Sort(Level::zero()),
        };
        let x_fvar = ctx.push_local_decl(Name::mk_simple("x"), x_ty.clone());

        let y_fvar = ctx.with_scope(|ctx| {
            let y_fvar = ctx.push_local_decl(Name::mk_simple("y"), x_ty.clone());
            assert_eq!(ctx.depth(), 2);
            y_fvar
        });

        // y should be gone after the scope
        assert_eq!(ctx.depth(), 1);
        assert!(ctx.get(&y_fvar).is_none());
        assert!(ctx.get(&x_fvar).is_some());
    }

    #[test]
    fn test_find_by_user_name() {
        let mut ctx = LocalContext::new();

        let ty = Expr {
            kind: ExprKind::Sort(Level::zero()),
        };
        let _x1 = ctx.push_local_decl(Name::mk_simple("x"), ty.clone());
        let y = ctx.push_local_decl(Name::mk_simple("y"), ty.clone());
        let x2 = ctx.push_local_decl(Name::mk_simple("x"), ty.clone());

        // Should find the most recent x
        assert_eq!(ctx.find_by_user_name(&Name::mk_simple("x")), Some(&x2));
        assert_eq!(ctx.find_by_user_name(&Name::mk_simple("y")), Some(&y));
        assert_eq!(ctx.find_by_user_name(&Name::mk_simple("z")), None);
    }
}
