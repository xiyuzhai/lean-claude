//! Metavariable management for the elaborator
//!
//! Metavariables represent "holes" in expressions that need to be filled
//! by the type inference algorithm.

use std::collections::HashMap;

use lean_kernel::{Expr, Name};

use crate::context::LocalContext;

/// Metavariable declaration
#[derive(Debug, Clone)]
pub struct MetavarDecl {
    /// Name of the metavariable
    pub name: Name,
    /// Type of the metavariable
    pub ty: Expr,
    /// Local context where the metavariable was created
    pub lctx: LocalContext,
}

/// Metavariable context - tracks all metavariables and their assignments
#[derive(Debug, Clone, Default)]
pub struct MetavarContext {
    /// Map from metavariable names to their declarations
    decls: HashMap<Name, MetavarDecl>,
    /// Map from metavariable names to their assigned values
    assignments: HashMap<Name, Expr>,
    /// Counter for generating unique metavariable names
    next_mvar_id: u64,
}

impl MetavarContext {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new metavariable with the given type and local context
    pub fn mk_metavar(&mut self, ty: Expr, lctx: LocalContext) -> Expr {
        let name = self.gen_fresh_mvar_name();
        let decl = MetavarDecl {
            name: name.clone(),
            ty,
            lctx,
        };
        self.decls.insert(name.clone(), decl);
        Expr::mvar(name)
    }

    /// Get the declaration of a metavariable
    pub fn get_decl(&self, name: &Name) -> Option<&MetavarDecl> {
        self.decls.get(name)
    }

    /// Get the type of a metavariable
    pub fn get_type(&self, name: &Name) -> Option<&Expr> {
        self.decls.get(name).map(|decl| &decl.ty)
    }

    /// Get the local context of a metavariable
    pub fn get_lctx(&self, name: &Name) -> Option<&LocalContext> {
        self.decls.get(name).map(|decl| &decl.lctx)
    }

    /// Check if a metavariable is assigned
    pub fn is_assigned(&self, name: &Name) -> bool {
        self.assignments.contains_key(name)
    }

    /// Get the assignment of a metavariable
    pub fn get_assignment(&self, name: &Name) -> Option<&Expr> {
        self.assignments.get(name)
    }

    /// Assign a value to a metavariable
    /// Returns an error if the metavariable is already assigned
    pub fn assign(&mut self, name: Name, value: Expr) -> Result<(), String> {
        if self.assignments.contains_key(&name) {
            return Err(format!("Metavariable {name} is already assigned"));
        }
        if !self.decls.contains_key(&name) {
            return Err(format!("Unknown metavariable {name}"));
        }
        self.assignments.insert(name, value);
        Ok(())
    }

    /// Instantiate metavariables in an expression
    /// Recursively replaces assigned metavariables with their values
    pub fn instantiate(&self, expr: &Expr) -> Expr {
        use lean_kernel::expr::ExprKind;

        match &expr.kind {
            ExprKind::MVar(name) => {
                if let Some(value) = self.assignments.get(name) {
                    // Recursively instantiate the assigned value
                    self.instantiate(value)
                } else {
                    expr.clone()
                }
            }
            ExprKind::App(f, a) => {
                let f_inst = self.instantiate(f);
                let a_inst = self.instantiate(a);
                if &f_inst == f.as_ref() && &a_inst == a.as_ref() {
                    expr.clone()
                } else {
                    Expr::app(f_inst, a_inst)
                }
            }
            ExprKind::Lam(name, ty, body, info) => {
                let ty_inst = self.instantiate(ty);
                let body_inst = self.instantiate(body);
                if &ty_inst == ty.as_ref() && &body_inst == body.as_ref() {
                    expr.clone()
                } else {
                    Expr::lam(name.clone(), ty_inst, body_inst, *info)
                }
            }
            ExprKind::Forall(name, ty, body, info) => {
                let ty_inst = self.instantiate(ty);
                let body_inst = self.instantiate(body);
                if &ty_inst == ty.as_ref() && &body_inst == body.as_ref() {
                    expr.clone()
                } else {
                    Expr::forall(name.clone(), ty_inst, body_inst, *info)
                }
            }
            ExprKind::Let(name, ty, val, body) => {
                let ty_inst = self.instantiate(ty);
                let val_inst = self.instantiate(val);
                let body_inst = self.instantiate(body);
                if &ty_inst == ty.as_ref()
                    && &val_inst == val.as_ref()
                    && &body_inst == body.as_ref()
                {
                    expr.clone()
                } else {
                    Expr::let_expr(name.clone(), ty_inst, val_inst, body_inst)
                }
            }
            ExprKind::Proj(name, idx, e) => {
                let e_inst = self.instantiate(e);
                if &e_inst == e.as_ref() {
                    expr.clone()
                } else {
                    Expr::proj(name.clone(), *idx, e_inst)
                }
            }
            ExprKind::MData(_mdata, e) => {
                let e_inst = self.instantiate(e);
                if &e_inst == e.as_ref() {
                    expr.clone()
                } else {
                    // MData constructor not available, just return the inner expression
                    e_inst
                }
            }
            // These cases don't contain subexpressions with metavariables
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(_, _)
            | ExprKind::Lit(_) => expr.clone(),
        }
    }

    /// Check if an expression contains unassigned metavariables
    pub fn has_unassigned_mvars(&self, expr: &Expr) -> bool {
        use lean_kernel::expr::ExprKind;

        match &expr.kind {
            ExprKind::MVar(name) => !self.is_assigned(name),
            ExprKind::App(f, a) => self.has_unassigned_mvars(f) || self.has_unassigned_mvars(a),
            ExprKind::Lam(_, ty, body, _) => {
                self.has_unassigned_mvars(ty) || self.has_unassigned_mvars(body)
            }
            ExprKind::Forall(_, ty, body, _) => {
                self.has_unassigned_mvars(ty) || self.has_unassigned_mvars(body)
            }
            ExprKind::Let(_, ty, val, body) => {
                self.has_unassigned_mvars(ty)
                    || self.has_unassigned_mvars(val)
                    || self.has_unassigned_mvars(body)
            }
            ExprKind::Proj(_, _, e) => self.has_unassigned_mvars(e),
            ExprKind::MData(_, e) => self.has_unassigned_mvars(e),
            _ => false,
        }
    }

    /// Generate a fresh metavariable name
    fn gen_fresh_mvar_name(&mut self) -> Name {
        let id = self.next_mvar_id;
        self.next_mvar_id += 1;
        Name::mk_simple(format!("?m.{id}"))
    }
}

#[cfg(test)]
mod tests {
    use lean_kernel::Level;

    use super::*;

    #[test]
    fn test_metavar_creation() {
        let mut mctx = MetavarContext::new();
        let lctx = LocalContext::new();

        let ty = Expr::sort(Level::zero());
        let mvar = mctx.mk_metavar(ty.clone(), lctx);

        if let lean_kernel::expr::ExprKind::MVar(name) = &mvar.kind {
            assert!(mctx.get_decl(name).is_some());
            assert_eq!(mctx.get_type(name), Some(&ty));
            assert!(!mctx.is_assigned(name));
        } else {
            panic!("Expected metavariable");
        }
    }

    #[test]
    fn test_metavar_assignment() {
        let mut mctx = MetavarContext::new();
        let lctx = LocalContext::new();

        let ty = Expr::sort(Level::zero());
        let mvar = mctx.mk_metavar(ty, lctx);

        if let lean_kernel::expr::ExprKind::MVar(name) = &mvar.kind {
            let value = Expr::const_expr("Nat.zero".into(), vec![]);
            assert!(mctx.assign(name.clone(), value.clone()).is_ok());
            assert!(mctx.is_assigned(name));
            assert_eq!(mctx.get_assignment(name), Some(&value));

            // Should error on double assignment
            assert!(mctx.assign(name.clone(), value).is_err());
        }
    }

    #[test]
    fn test_instantiate() {
        let mut mctx = MetavarContext::new();
        let lctx = LocalContext::new();

        // Create two metavariables
        let ty = Expr::sort(Level::zero());
        let m1 = mctx.mk_metavar(ty.clone(), lctx.clone());
        let m2 = mctx.mk_metavar(ty, lctx);

        // Create an expression with metavariables: m1 m2
        let expr = Expr::app(m1.clone(), m2.clone());

        // Assign m1
        if let lean_kernel::expr::ExprKind::MVar(m1_name) = &m1.kind {
            let val1 = Expr::const_expr("f".into(), vec![]);
            mctx.assign(m1_name.clone(), val1.clone()).unwrap();

            // Instantiate should replace m1 but not m2
            let inst = mctx.instantiate(&expr);
            if let lean_kernel::expr::ExprKind::App(f, a) = &inst.kind {
                assert_eq!(**f, val1);
                assert_eq!(**a, m2);
            } else {
                panic!("Expected application");
            }
        }
    }

    #[test]
    fn test_has_unassigned_mvars() {
        let mut mctx = MetavarContext::new();
        let lctx = LocalContext::new();

        let ty = Expr::sort(Level::zero());
        let m1 = mctx.mk_metavar(ty.clone(), lctx.clone());
        let m2 = mctx.mk_metavar(ty, lctx);

        let expr = Expr::app(m1.clone(), m2);
        assert!(mctx.has_unassigned_mvars(&expr));

        // Assign both metavariables
        if let lean_kernel::expr::ExprKind::MVar(m1_name) = &m1.kind {
            mctx.assign(m1_name.clone(), Expr::const_expr("x".into(), vec![]))
                .unwrap();
        }

        // Still has m2 unassigned
        assert!(mctx.has_unassigned_mvars(&expr));
    }
}
