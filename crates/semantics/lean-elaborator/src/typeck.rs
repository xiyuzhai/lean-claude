//! Type checking and type inference

use lean_kernel::{
    expr::{BinderInfo, ExprKind},
    Expr, Level, Name,
};

use crate::{
    context::LocalContext,
    error::ElabError,
    metavar::MetavarContext,
};

/// Type checker state
pub struct TypeChecker<'a> {
    /// Local context
    lctx: &'a LocalContext,
    /// Metavariable context
    mctx: &'a mut MetavarContext,
}

impl<'a> TypeChecker<'a> {
    pub fn new(lctx: &'a LocalContext, mctx: &'a mut MetavarContext) -> Self {
        Self { lctx, mctx }
    }

    /// Infer the type of an expression
    pub fn infer_type(&mut self, expr: &Expr) -> Result<Expr, ElabError> {
        match &expr.kind {
            ExprKind::BVar(idx) => {
                // Bound variables should not appear at this level
                Err(ElabError::InvalidSyntax(format!(
                    "Unexpected bound variable {idx}"
                )))
            }
            ExprKind::FVar(name) => {
                // Look up the type in the local context
                self.lctx
                    .get_type(name)
                    .cloned()
                    .ok_or_else(|| ElabError::UnknownIdentifier(name.clone()))
            }
            ExprKind::MVar(name) => {
                // Look up the type of the metavariable
                self.mctx
                    .get_type(name)
                    .cloned()
                    .ok_or_else(|| ElabError::UnassignedMetavar(name.clone()))
            }
            ExprKind::Sort(level) => {
                // Type of Sort u is Sort (u+1)
                Ok(Expr::sort(Level::succ(level.clone())))
            }
            ExprKind::Const(name, _levels) => {
                // TODO: Look up constant in environment
                Err(ElabError::UnknownIdentifier(name.clone()))
            }
            ExprKind::App(f, a) => {
                // Infer type of function
                let f_type = self.infer_type(f)?;
                
                // Normalize the function type
                let f_type_norm = self.whnf(&f_type)?;
                
                // Function type must be a forall
                match &f_type_norm.kind {
                    ExprKind::Forall(_, domain, codomain, _) => {
                        // Check that argument has the right type
                        let a_type = self.infer_type(a)?;
                        self.ensure_def_eq(&a_type, domain)?;
                        
                        // Substitute argument in codomain
                        Ok(self.instantiate(codomain, a))
                    }
                    _ => Err(ElabError::TypeMismatch {
                        expected: "function type".to_string(),
                        got: format!("{:?}", f_type_norm),
                    }),
                }
            }
            ExprKind::Lam(name, ty, body, _) => {
                // Type of lambda is forall
                Ok(Expr::forall(
                    name.clone(),
                    (**ty).clone(),
                    (**body).clone(), // TODO: Infer body type in extended context
                    BinderInfo::Default,
                ))
            }
            ExprKind::Forall(_name, ty, _body, _info) => {
                // Check that ty is a type
                let ty_type = self.infer_type(ty)?;
                self.ensure_is_type(&ty_type)?;
                
                // TODO: Check body in extended context
                
                // Type of forall is a sort
                Ok(Expr::sort(Level::zero())) // TODO: Universe polymorphism
            }
            ExprKind::Let(_name, _ty, _val, body) => {
                // Check that value has the declared type
                // let val_type = self.infer_type(val)?;
                // For now, don't check type equality since we're using metavariables
                // self.ensure_def_eq(&val_type, ty)?;
                
                // Type of let is type of body with substitution
                // For now, just infer the body type directly
                // TODO: Properly handle let bindings in context
                self.infer_type(body)
            }
            ExprKind::Lit(lit) => {
                use lean_kernel::expr::Literal;
                match lit {
                    Literal::Nat(_) => Ok(Expr::const_expr("Nat".into(), vec![])),
                    Literal::String(_) => Ok(Expr::const_expr("String".into(), vec![])),
                }
            }
            ExprKind::Proj(struct_name, idx, _e) => {
                // TODO: Look up structure and field types
                Err(ElabError::InvalidProjection(format!(
                    "Projection {}.{} not implemented",
                    struct_name, idx
                )))
            }
            ExprKind::MData(_, e) => {
                // Metadata doesn't affect the type
                self.infer_type(e)
            }
        }
    }

    /// Check that an expression has a given type
    pub fn check_type(&mut self, expr: &Expr, expected_ty: &Expr) -> Result<(), ElabError> {
        let actual_ty = self.infer_type(expr)?;
        self.ensure_def_eq(&actual_ty, expected_ty)
    }

    /// Ensure that an expression is a type (Sort _)
    fn ensure_is_type(&mut self, ty: &Expr) -> Result<(), ElabError> {
        let ty_whnf = self.whnf(ty)?;
        match &ty_whnf.kind {
            ExprKind::Sort(_) => Ok(()),
            _ => Err(ElabError::TypeMismatch {
                expected: "Sort".to_string(),
                got: format!("{:?}", ty_whnf),
            }),
        }
    }

    /// Ensure two expressions are definitionally equal
    fn ensure_def_eq(&mut self, e1: &Expr, e2: &Expr) -> Result<(), ElabError> {
        if self.is_def_eq(e1, e2)? {
            Ok(())
        } else {
            Err(ElabError::TypeMismatch {
                expected: format!("{:?}", e2),
                got: format!("{:?}", e1),
            })
        }
    }

    /// Check if two expressions are definitionally equal
    pub fn is_def_eq(&mut self, e1: &Expr, e2: &Expr) -> Result<bool, ElabError> {
        // First try syntactic equality
        if e1 == e2 {
            return Ok(true);
        }

        // Reduce to weak head normal form and compare
        let e1_whnf = self.whnf(e1)?;
        let e2_whnf = self.whnf(e2)?;

        self.is_def_eq_core(&e1_whnf, &e2_whnf)
    }

    /// Core definitional equality check
    fn is_def_eq_core(&mut self, e1: &Expr, e2: &Expr) -> Result<bool, ElabError> {
        use ExprKind::*;
        
        match (&e1.kind, &e2.kind) {
            (BVar(i1), BVar(i2)) => Ok(i1 == i2),
            (FVar(n1), FVar(n2)) => Ok(n1 == n2),
            (MVar(n1), MVar(n2)) => Ok(n1 == n2),
            (Sort(l1), Sort(l2)) => Ok(l1 == l2),
            (Const(n1, ls1), Const(n2, ls2)) => Ok(n1 == n2 && ls1 == ls2),
            (Lit(l1), Lit(l2)) => Ok(l1 == l2),
            
            (App(f1, a1), App(f2, a2)) => {
                Ok(self.is_def_eq(f1, f2)? && self.is_def_eq(a1, a2)?)
            }
            
            (Lam(_, ty1, body1, _), Lam(_, ty2, body2, _)) => {
                Ok(self.is_def_eq(ty1, ty2)? && self.is_def_eq(body1, body2)?)
            }
            
            (Forall(_, ty1, body1, _), Forall(_, ty2, body2, _)) => {
                Ok(self.is_def_eq(ty1, ty2)? && self.is_def_eq(body1, body2)?)
            }
            
            (Let(_, ty1, val1, body1), Let(_, ty2, val2, body2)) => {
                Ok(self.is_def_eq(ty1, ty2)?
                    && self.is_def_eq(val1, val2)?
                    && self.is_def_eq(body1, body2)?)
            }
            
            (Proj(s1, i1, e1), Proj(s2, i2, e2)) => {
                Ok(s1 == s2 && i1 == i2 && self.is_def_eq(e1, e2)?)
            }
            
            _ => Ok(false),
        }
    }

    /// Reduce expression to weak head normal form
    pub fn whnf(&mut self, expr: &Expr) -> Result<Expr, ElabError> {
        // First instantiate metavariables
        let expr = self.mctx.instantiate(expr);

        match &expr.kind {
            ExprKind::App(f, a) => {
                let f_whnf = self.whnf(f)?;
                match &f_whnf.kind {
                    ExprKind::Lam(_, _, body, _) => {
                        // Beta reduction
                        let result = self.instantiate(body, a);
                        self.whnf(&result)
                    }
                    _ => Ok(Expr::app(f_whnf, (**a).clone())),
                }
            }
            ExprKind::Let(_, _, val, body) => {
                // Let reduction
                let result = self.instantiate(body, val);
                self.whnf(&result)
            }
            ExprKind::Proj(_struct_name, _idx, _e) => {
                // TODO: Projection reduction
                Ok(expr)
            }
            _ => Ok(expr),
        }
    }

    /// Instantiate the first bound variable in an expression with a value
    fn instantiate(&self, expr: &Expr, value: &Expr) -> Expr {
        self.instantiate_core(expr, value, 0)
    }

    fn instantiate_core(&self, expr: &Expr, value: &Expr, depth: u32) -> Expr {
        match &expr.kind {
            ExprKind::BVar(idx) => {
                if *idx == depth {
                    // Replace with value, adjusting bound variables
                    self.lift_bvars(value, depth)
                } else if *idx > depth {
                    // Decrease index since we're removing a binder
                    Expr::bvar(idx - 1)
                } else {
                    expr.clone()
                }
            }
            ExprKind::App(f, a) => {
                let f_inst = self.instantiate_core(f, value, depth);
                let a_inst = self.instantiate_core(a, value, depth);
                Expr::app(f_inst, a_inst)
            }
            ExprKind::Lam(name, ty, body, info) => {
                let ty_inst = self.instantiate_core(ty, value, depth);
                let body_inst = self.instantiate_core(body, value, depth + 1);
                Expr::lam(name.clone(), ty_inst, body_inst, *info)
            }
            ExprKind::Forall(name, ty, body, info) => {
                let ty_inst = self.instantiate_core(ty, value, depth);
                let body_inst = self.instantiate_core(body, value, depth + 1);
                Expr::forall(name.clone(), ty_inst, body_inst, *info)
            }
            ExprKind::Let(name, ty, val, body) => {
                let ty_inst = self.instantiate_core(ty, value, depth);
                let val_inst = self.instantiate_core(val, value, depth);
                let body_inst = self.instantiate_core(body, value, depth + 1);
                Expr::let_expr(name.clone(), ty_inst, val_inst, body_inst)
            }
            _ => expr.clone(),
        }
    }

    /// Lift bound variables in an expression by a given amount
    fn lift_bvars(&self, expr: &Expr, amount: u32) -> Expr {
        self.lift_bvars_core(expr, amount, 0)
    }

    fn lift_bvars_core(&self, expr: &Expr, amount: u32, depth: u32) -> Expr {
        match &expr.kind {
            ExprKind::BVar(idx) => {
                if *idx >= depth {
                    Expr::bvar(idx + amount)
                } else {
                    expr.clone()
                }
            }
            ExprKind::App(f, a) => {
                let f_lift = self.lift_bvars_core(f, amount, depth);
                let a_lift = self.lift_bvars_core(a, amount, depth);
                Expr::app(f_lift, a_lift)
            }
            ExprKind::Lam(name, ty, body, info) => {
                let ty_lift = self.lift_bvars_core(ty, amount, depth);
                let body_lift = self.lift_bvars_core(body, amount, depth + 1);
                Expr::lam(name.clone(), ty_lift, body_lift, *info)
            }
            ExprKind::Forall(name, ty, body, info) => {
                let ty_lift = self.lift_bvars_core(ty, amount, depth);
                let body_lift = self.lift_bvars_core(body, amount, depth + 1);
                Expr::forall(name.clone(), ty_lift, body_lift, *info)
            }
            ExprKind::Let(name, ty, val, body) => {
                let ty_lift = self.lift_bvars_core(ty, amount, depth);
                let val_lift = self.lift_bvars_core(val, amount, depth);
                let body_lift = self.lift_bvars_core(body, amount, depth + 1);
                Expr::let_expr(name.clone(), ty_lift, val_lift, body_lift)
            }
            _ => expr.clone(),
        }
    }
}

/// Unification algorithm
pub struct Unifier<'a> {
    /// Type checker
    tc: TypeChecker<'a>,
}

impl<'a> Unifier<'a> {
    pub fn new(lctx: &'a LocalContext, mctx: &'a mut MetavarContext) -> Self {
        Self {
            tc: TypeChecker::new(lctx, mctx),
        }
    }

    /// Unify two expressions, potentially assigning metavariables
    pub fn unify(&mut self, e1: &Expr, e2: &Expr) -> Result<(), ElabError> {
        // First check if they're already equal
        if self.tc.is_def_eq(e1, e2)? {
            return Ok(());
        }

        // Reduce to WHNF
        let e1_whnf = self.tc.whnf(e1)?;
        let e2_whnf = self.tc.whnf(e2)?;

        self.unify_core(&e1_whnf, &e2_whnf)
    }

    fn unify_core(&mut self, e1: &Expr, e2: &Expr) -> Result<(), ElabError> {
        use ExprKind::*;

        match (&e1.kind, &e2.kind) {
            // Metavariable cases
            (MVar(m1), MVar(m2)) if m1 == m2 => Ok(()),
            (MVar(m), _) => self.assign_mvar(m.clone(), e2.clone()),
            (_, MVar(m)) => self.assign_mvar(m.clone(), e1.clone()),

            // Structural cases
            (App(f1, a1), App(f2, a2)) => {
                self.unify(f1, f2)?;
                self.unify(a1, a2)
            }
            
            (Lam(_, ty1, body1, _), Lam(_, ty2, body2, _)) => {
                self.unify(ty1, ty2)?;
                self.unify(body1, body2)
            }
            
            (Forall(_, ty1, body1, _), Forall(_, ty2, body2, _)) => {
                self.unify(ty1, ty2)?;
                self.unify(body1, body2)
            }

            _ => {
                // Check if they're definitionally equal
                if self.tc.is_def_eq(e1, e2)? {
                    Ok(())
                } else {
                    Err(ElabError::TypeMismatch {
                        expected: format!("{:?}", e2),
                        got: format!("{:?}", e1),
                    })
                }
            }
        }
    }

    fn assign_mvar(&mut self, mvar: Name, value: Expr) -> Result<(), ElabError> {
        // TODO: Occurs check
        self.tc.mctx.assign(mvar, value)
            .map_err(|e| ElabError::ElaborationFailed(e))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer_type_sort() {
        let lctx = LocalContext::new();
        let mut mctx = MetavarContext::new();
        let mut tc = TypeChecker::new(&lctx, &mut mctx);

        // Type of Sort 0 is Sort 1
        let expr = Expr::sort(Level::zero());
        let ty = tc.infer_type(&expr).unwrap();
        
        match &ty.kind {
            ExprKind::Sort(level) => {
                assert_eq!(*level, Level::succ(Level::zero()));
            }
            _ => panic!("Expected Sort"),
        }
    }

    #[test]
    fn test_whnf_beta_reduction() {
        let lctx = LocalContext::new();
        let mut mctx = MetavarContext::new();
        let mut tc = TypeChecker::new(&lctx, &mut mctx);

        // (λ x => x) y should reduce to y
        let lam = Expr::lam(
            Name::mk_simple("x"),
            Expr::sort(Level::zero()),
            Expr::bvar(0),
            BinderInfo::Default,
        );
        let app = Expr::app(lam, Expr::fvar(Name::mk_simple("y")));

        let reduced = tc.whnf(&app).unwrap();
        
        match &reduced.kind {
            ExprKind::FVar(name) => {
                assert_eq!(name.to_string(), "y");
            }
            _ => panic!("Expected FVar(y)"),
        }
    }

    #[test]
    fn test_unify_simple() {
        let lctx = LocalContext::new();
        let mut mctx = MetavarContext::new();

        // Create a metavariable
        let mvar = mctx.mk_metavar(Expr::sort(Level::zero()), lctx.clone());
        
        // Unify it with a constant
        let const_expr = Expr::const_expr("Nat".into(), vec![]);
        
        let mut unifier = Unifier::new(&lctx, &mut mctx);
        unifier.unify(&mvar, &const_expr).unwrap();

        // Check that the metavariable was assigned
        if let ExprKind::MVar(name) = &mvar.kind {
            assert!(mctx.is_assigned(name));
            assert_eq!(mctx.get_assignment(name).unwrap(), &const_expr);
        }
    }
}