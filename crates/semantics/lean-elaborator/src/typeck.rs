//! Type checking and type inference

use lean_kernel::{
    environment::Environment,
    expr::{BinderInfo, ExprKind},
    Expr, Level, Name,
};

use crate::{context::LocalContext, error::ElabError, metavar::MetavarContext};

/// Type checker state
pub struct TypeChecker<'a> {
    /// Local context
    lctx: &'a LocalContext,
    /// Metavariable context
    mctx: &'a mut MetavarContext,
    /// Environment for constant lookup
    env: Option<&'a Environment>,
}

impl<'a> TypeChecker<'a> {
    pub fn new(lctx: &'a LocalContext, mctx: &'a mut MetavarContext) -> Self {
        Self {
            lctx,
            mctx,
            env: None,
        }
    }

    pub fn with_env(
        lctx: &'a LocalContext,
        mctx: &'a mut MetavarContext,
        env: &'a Environment,
    ) -> Self {
        Self {
            lctx,
            mctx,
            env: Some(env),
        }
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
            ExprKind::Const(name, levels) => {
                // Look up constant in environment
                if let Some(env) = self.env {
                    if let Some(decl) = env.get_declaration(name) {
                        // TODO: Proper universe level instantiation
                        // For now, just return the declared type
                        if levels.is_empty() && decl.universe_params.is_empty() {
                            // No universe polymorphism
                            Ok(decl.ty.clone())
                        } else if levels.len() == decl.universe_params.len() {
                            // Universe instantiation needed
                            // TODO: Implement proper universe substitution
                            Ok(decl.ty.clone())
                        } else {
                            Err(ElabError::UniverseLevelError(format!(
                                "Universe level mismatch for {}: expected {}, got {}",
                                name,
                                decl.universe_params.len(),
                                levels.len()
                            )))
                        }
                    } else {
                        Err(ElabError::UnknownIdentifier(name.clone()))
                    }
                } else {
                    // No environment - create metavariable as fallback
                    let const_type = self
                        .mctx
                        .mk_metavar(Expr::sort(Level::zero()), self.lctx.clone());
                    Ok(const_type)
                }
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
                        got: format!("{f_type_norm:?}"),
                    }),
                }
            }
            ExprKind::Lam(name, ty, body, info) => {
                // Check that the domain is a type
                let ty_type = self.infer_type(ty)?;
                self.ensure_is_type(&ty_type)?;

                // Create a fresh fvar for the lambda parameter
                let mut extended_lctx = self.lctx.clone();
                let fvar_id = extended_lctx.push_local_decl(name.clone(), (**ty).clone());

                // Infer the type of the body in the extended context
                let mut extended_tc = TypeChecker::new(&extended_lctx, self.mctx);

                // Substitute the parameter in the body with the fresh fvar
                let body_with_fvar = TypeChecker::instantiate_bvar_with_fvar(body, 0, &fvar_id);
                let body_type = extended_tc.infer_type(&body_with_fvar)?;

                // Abstract the fvar back to a bound variable in the body type
                let body_type_abstracted =
                    TypeChecker::abstract_fvar_to_bvar(&body_type, &fvar_id, 0);

                // Type of lambda is forall
                Ok(Expr::forall(
                    name.clone(),
                    (**ty).clone(),
                    body_type_abstracted,
                    *info,
                ))
            }
            ExprKind::Forall(name, ty, body, _info) => {
                // Check that ty is a type
                let ty_type = self.infer_type(ty)?;
                self.ensure_is_type(&ty_type)?;

                // Get the universe level of the domain type
                let domain_level = match &ty_type.kind {
                    ExprKind::Sort(level) => level.clone(),
                    _ => Level::zero(), // Fallback
                };

                // Create a fresh fvar for the forall parameter
                let mut extended_lctx = self.lctx.clone();
                let fvar_id = extended_lctx.push_local_decl(name.clone(), (**ty).clone());

                // Check the body type in the extended context
                let mut extended_tc = TypeChecker::new(&extended_lctx, self.mctx);

                // Substitute the parameter in the body with the fresh fvar
                let body_with_fvar = TypeChecker::instantiate_bvar_with_fvar(body, 0, &fvar_id);
                let body_type = extended_tc.infer_type(&body_with_fvar)?;

                // Ensure the body is a type
                extended_tc.ensure_is_type(&body_type)?;

                // Get the universe level of the codomain type
                let codomain_level = match &body_type.kind {
                    ExprKind::Sort(level) => level.clone(),
                    _ => Level::zero(), // Fallback
                };

                // Type of forall is the max of domain and codomain levels
                // TODO: Implement proper universe level calculation
                let result_level = Level::max(domain_level, codomain_level);
                Ok(Expr::sort(result_level))
            }
            ExprKind::Let(name, ty, val, body) => {
                // Check that value has the declared type
                let val_type = self.infer_type(val)?;
                self.ensure_def_eq(&val_type, ty)?;

                // Create a fresh fvar for the let binding
                let mut extended_lctx = self.lctx.clone();
                let fvar_id = extended_lctx.push_local_def(
                    name.clone(),
                    Some((**ty).clone()),
                    (**val).clone(),
                );

                // Infer the type of the body in the extended context
                let mut extended_tc = TypeChecker::new(&extended_lctx, self.mctx);

                // Substitute the let variable in the body with the fresh fvar
                let body_with_fvar = TypeChecker::instantiate_bvar_with_fvar(body, 0, &fvar_id);
                let body_type = extended_tc.infer_type(&body_with_fvar)?;

                // Abstract the fvar back to a bound variable in the body type
                let body_type_abstracted =
                    TypeChecker::abstract_fvar_to_bvar(&body_type, &fvar_id, 0);

                // Now substitute the let value into the body type
                Ok(self.instantiate(&body_type_abstracted, val))
            }
            ExprKind::Lit(lit) => {
                use lean_kernel::expr::Literal;
                match lit {
                    Literal::Nat(_) => Ok(Expr::const_expr("Nat".into(), vec![])),
                    Literal::String(_) => Ok(Expr::const_expr("String".into(), vec![])),
                }
            }
            ExprKind::Proj(struct_name, idx, e) => {
                // Infer the type of the expression being projected
                let e_type = self.infer_type(e)?;

                // TODO: Proper structure field lookup
                // For now, create a metavariable for the result type
                let result_type = self
                    .mctx
                    .mk_metavar(Expr::sort(Level::zero()), self.lctx.clone());

                // TODO: Add proper projection type inference:
                // 1. Check that e_type is a structure type
                // 2. Look up the field at index idx in struct_name
                // 3. Instantiate the field type with the expression

                Ok(result_type)
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
                got: format!("{ty_whnf:?}"),
            }),
        }
    }

    /// Ensure two expressions are definitionally equal
    fn ensure_def_eq(&mut self, e1: &Expr, e2: &Expr) -> Result<(), ElabError> {
        if self.is_def_eq(e1, e2)? {
            Ok(())
        } else {
            Err(ElabError::TypeMismatch {
                expected: format!("{e2:?}"),
                got: format!("{e1:?}"),
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

            (App(f1, a1), App(f2, a2)) => Ok(self.is_def_eq(f1, f2)? && self.is_def_eq(a1, a2)?),

            (Lam(_, ty1, body1, _), Lam(_, ty2, body2, _)) => {
                Ok(self.is_def_eq(ty1, ty2)? && self.is_def_eq(body1, body2)?)
            }

            (Forall(_, ty1, body1, _), Forall(_, ty2, body2, _)) => {
                Ok(self.is_def_eq(ty1, ty2)? && self.is_def_eq(body1, body2)?)
            }

            (Let(_, ty1, val1, body1), Let(_, ty2, val2, body2)) => Ok(self.is_def_eq(ty1, ty2)?
                && self.is_def_eq(val1, val2)?
                && self.is_def_eq(body1, body2)?),

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

    /// Instantiate a specific bound variable with a free variable
    fn instantiate_bvar_with_fvar(expr: &Expr, bvar_idx: u32, fvar_id: &Name) -> Expr {
        Self::instantiate_bvar_with_fvar_core(expr, bvar_idx, fvar_id, 0)
    }

    fn instantiate_bvar_with_fvar_core(
        expr: &Expr,
        target_bvar: u32,
        fvar_id: &Name,
        depth: u32,
    ) -> Expr {
        match &expr.kind {
            ExprKind::BVar(idx) => {
                if *idx == target_bvar + depth {
                    // Replace with fvar
                    Expr::fvar(fvar_id.clone())
                } else {
                    expr.clone()
                }
            }
            ExprKind::App(f, a) => {
                let f_inst = Self::instantiate_bvar_with_fvar_core(f, target_bvar, fvar_id, depth);
                let a_inst = Self::instantiate_bvar_with_fvar_core(a, target_bvar, fvar_id, depth);
                Expr::app(f_inst, a_inst)
            }
            ExprKind::Lam(name, ty, body, info) => {
                let ty_inst =
                    Self::instantiate_bvar_with_fvar_core(ty, target_bvar, fvar_id, depth);
                let body_inst =
                    Self::instantiate_bvar_with_fvar_core(body, target_bvar, fvar_id, depth + 1);
                Expr::lam(name.clone(), ty_inst, body_inst, *info)
            }
            ExprKind::Forall(name, ty, body, info) => {
                let ty_inst =
                    Self::instantiate_bvar_with_fvar_core(ty, target_bvar, fvar_id, depth);
                let body_inst =
                    Self::instantiate_bvar_with_fvar_core(body, target_bvar, fvar_id, depth + 1);
                Expr::forall(name.clone(), ty_inst, body_inst, *info)
            }
            ExprKind::Let(name, ty, val, body) => {
                let ty_inst =
                    Self::instantiate_bvar_with_fvar_core(ty, target_bvar, fvar_id, depth);
                let val_inst =
                    Self::instantiate_bvar_with_fvar_core(val, target_bvar, fvar_id, depth);
                let body_inst =
                    Self::instantiate_bvar_with_fvar_core(body, target_bvar, fvar_id, depth + 1);
                Expr::let_expr(name.clone(), ty_inst, val_inst, body_inst)
            }
            _ => expr.clone(),
        }
    }

    /// Abstract a free variable to a bound variable
    fn abstract_fvar_to_bvar(expr: &Expr, fvar_id: &Name, target_bvar: u32) -> Expr {
        Self::abstract_fvar_to_bvar_core(expr, fvar_id, target_bvar, 0)
    }

    fn abstract_fvar_to_bvar_core(
        expr: &Expr,
        fvar_id: &Name,
        target_bvar: u32,
        depth: u32,
    ) -> Expr {
        match &expr.kind {
            ExprKind::FVar(name) if name == fvar_id => {
                // Replace with bvar
                Expr::bvar(target_bvar + depth)
            }
            ExprKind::BVar(idx) => {
                // Adjust bound variables that are "above" our target
                if *idx >= target_bvar + depth {
                    Expr::bvar(idx + 1)
                } else {
                    expr.clone()
                }
            }
            ExprKind::App(f, a) => {
                let f_abs = Self::abstract_fvar_to_bvar_core(f, fvar_id, target_bvar, depth);
                let a_abs = Self::abstract_fvar_to_bvar_core(a, fvar_id, target_bvar, depth);
                Expr::app(f_abs, a_abs)
            }
            ExprKind::Lam(name, ty, body, info) => {
                let ty_abs = Self::abstract_fvar_to_bvar_core(ty, fvar_id, target_bvar, depth);
                let body_abs =
                    Self::abstract_fvar_to_bvar_core(body, fvar_id, target_bvar, depth + 1);
                Expr::lam(name.clone(), ty_abs, body_abs, *info)
            }
            ExprKind::Forall(name, ty, body, info) => {
                let ty_abs = Self::abstract_fvar_to_bvar_core(ty, fvar_id, target_bvar, depth);
                let body_abs =
                    Self::abstract_fvar_to_bvar_core(body, fvar_id, target_bvar, depth + 1);
                Expr::forall(name.clone(), ty_abs, body_abs, *info)
            }
            ExprKind::Let(name, ty, val, body) => {
                let ty_abs = Self::abstract_fvar_to_bvar_core(ty, fvar_id, target_bvar, depth);
                let val_abs = Self::abstract_fvar_to_bvar_core(val, fvar_id, target_bvar, depth);
                let body_abs =
                    Self::abstract_fvar_to_bvar_core(body, fvar_id, target_bvar, depth + 1);
                Expr::let_expr(name.clone(), ty_abs, val_abs, body_abs)
            }
            _ => expr.clone(),
        }
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

    #[allow(clippy::only_used_in_recursion)]
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

    pub fn with_env(
        lctx: &'a LocalContext,
        mctx: &'a mut MetavarContext,
        env: &'a Environment,
    ) -> Self {
        Self {
            tc: TypeChecker::with_env(lctx, mctx, env),
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
            (MVar(m1), MVar(_m2)) => {
                // Flex-flex case: assign one to the other
                // Prefer assigning the "younger" metavariable
                self.assign_mvar(m1.clone(), e2.clone())
            }
            (MVar(m), _) => {
                // Flex-rigid case
                self.unify_flex_rigid(m.clone(), e2)
            }
            (_, MVar(m)) => {
                // Rigid-flex case (symmetric)
                self.unify_flex_rigid(m.clone(), e1)
            }

            // Structural cases
            (BVar(i1), BVar(i2)) if i1 == i2 => Ok(()),
            (FVar(n1), FVar(n2)) if n1 == n2 => Ok(()),
            (Sort(l1), Sort(l2)) if l1 == l2 => Ok(()),
            (Const(n1, ls1), Const(n2, ls2)) if n1 == n2 && ls1 == ls2 => Ok(()),
            (Lit(l1), Lit(l2)) if l1 == l2 => Ok(()),

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

            (Let(_, ty1, val1, body1), Let(_, ty2, val2, body2)) => {
                self.unify(ty1, ty2)?;
                self.unify(val1, val2)?;
                self.unify(body1, body2)
            }

            (Proj(s1, i1, e1), Proj(s2, i2, e2)) if s1 == s2 && i1 == i2 => self.unify(e1, e2),

            _ => {
                // Try to reduce and unify again
                let e1_reduced = self.tc.whnf(e1)?;
                let e2_reduced = self.tc.whnf(e2)?;

                if e1_reduced != *e1 || e2_reduced != *e2 {
                    // Something reduced, try again
                    self.unify(&e1_reduced, &e2_reduced)
                } else {
                    // Nothing to reduce, check definitional equality
                    if self.tc.is_def_eq(e1, e2)? {
                        Ok(())
                    } else {
                        Err(ElabError::TypeMismatch {
                            expected: self.expr_to_string(e2),
                            got: self.expr_to_string(e1),
                        })
                    }
                }
            }
        }
    }

    /// Unify a metavariable with a rigid term
    fn unify_flex_rigid(&mut self, mvar: Name, rigid: &Expr) -> Result<(), ElabError> {
        // Check if the rigid term is a function application with the metavariable
        // This handles cases like ?m a =?= f a where we can set ?m := f
        if let ExprKind::App(_f, _a) = &rigid.kind {
            // Try pattern unification if applicable
            if let Ok(solution) = self.try_pattern_unification(&mvar, rigid) {
                return self.assign_mvar(mvar, solution);
            }
        }

        // Default case: just assign if occurs check passes
        self.assign_mvar(mvar, rigid.clone())
    }

    /// Try to solve metavariable using pattern unification
    /// This is a simplified version that handles basic cases
    fn try_pattern_unification(&self, _mvar: &Name, _pattern: &Expr) -> Result<Expr, ElabError> {
        // TODO: Implement proper pattern unification
        // For now, just fail and fall back to simple assignment
        Err(ElabError::CannotInferType)
    }

    fn assign_mvar(&mut self, mvar: Name, value: Expr) -> Result<(), ElabError> {
        // Occurs check: ensure the metavariable doesn't occur in the value
        if self.occurs_check(&mvar, &value) {
            return Err(ElabError::ElaborationFailed(format!(
                "Occurs check failed: ?{} occurs in {}",
                mvar,
                self.expr_to_string(&value)
            )));
        }

        // Assign the metavariable
        self.tc
            .mctx
            .assign(mvar, value)
            .map_err(ElabError::ElaborationFailed)
    }

    /// Check if a metavariable occurs in an expression
    fn occurs_check(&self, mvar: &Name, expr: &Expr) -> bool {
        self.occurs_check_core(mvar, expr, 0)
    }

    #[allow(clippy::only_used_in_recursion)]
    fn occurs_check_core(&self, mvar: &Name, expr: &Expr, _depth: u32) -> bool {
        match &expr.kind {
            ExprKind::MVar(name) => name == mvar,
            ExprKind::App(f, a) => {
                self.occurs_check_core(mvar, f, _depth) || self.occurs_check_core(mvar, a, _depth)
            }
            ExprKind::Lam(_, ty, body, _) => {
                self.occurs_check_core(mvar, ty, _depth)
                    || self.occurs_check_core(mvar, body, _depth + 1)
            }
            ExprKind::Forall(_, ty, body, _) => {
                self.occurs_check_core(mvar, ty, _depth)
                    || self.occurs_check_core(mvar, body, _depth + 1)
            }
            ExprKind::Let(_, ty, val, body) => {
                self.occurs_check_core(mvar, ty, _depth)
                    || self.occurs_check_core(mvar, val, _depth)
                    || self.occurs_check_core(mvar, body, _depth + 1)
            }
            ExprKind::Proj(_, _, e) => self.occurs_check_core(mvar, e, _depth),
            ExprKind::MData(_, e) => self.occurs_check_core(mvar, e, _depth),
            _ => false,
        }
    }

    /// Convert expression to string for error messages
    fn expr_to_string(&self, expr: &Expr) -> String {
        format!("{expr:?}") // Simple implementation for now
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

    #[test]
    fn test_unify_flex_flex() {
        let lctx = LocalContext::new();
        let mut mctx = MetavarContext::new();

        // Create two metavariables
        let mvar1 = mctx.mk_metavar(Expr::sort(Level::zero()), lctx.clone());
        let mvar2 = mctx.mk_metavar(Expr::sort(Level::zero()), lctx.clone());

        let mut unifier = Unifier::new(&lctx, &mut mctx);
        unifier.unify(&mvar1, &mvar2).unwrap();

        // One should be assigned to the other
        match (&mvar1.kind, &mvar2.kind) {
            (ExprKind::MVar(name1), ExprKind::MVar(_name2)) => {
                assert!(mctx.is_assigned(name1));
            }
            _ => panic!("Expected metavariables"),
        }
    }

    #[test]
    fn test_unify_occurs_check() {
        let lctx = LocalContext::new();
        let mut mctx = MetavarContext::new();

        // Create a metavariable
        let mvar = mctx.mk_metavar(Expr::sort(Level::zero()), lctx.clone());

        // Try to unify ?m with f(?m) - should fail occurs check
        let app = Expr::app(Expr::const_expr("f".into(), vec![]), mvar.clone());

        let mut unifier = Unifier::new(&lctx, &mut mctx);
        let result = unifier.unify(&mvar, &app);

        assert!(result.is_err());
        if let Err(ElabError::ElaborationFailed(msg)) = result {
            assert!(msg.contains("Occurs check failed"));
        }
    }

    #[test]
    fn test_unify_structural() {
        let lctx = LocalContext::new();
        let mut mctx = MetavarContext::new();

        // Create metavariables
        let mvar1 = mctx.mk_metavar(Expr::sort(Level::zero()), lctx.clone());
        let mvar2 = mctx.mk_metavar(Expr::sort(Level::zero()), lctx.clone());

        // Create structural expressions: f ?m1 and f ?m2
        let expr1 = Expr::app(Expr::const_expr("f".into(), vec![]), mvar1);
        let expr2 = Expr::app(Expr::const_expr("f".into(), vec![]), mvar2);

        let mut unifier = Unifier::new(&lctx, &mut mctx);
        unifier.unify(&expr1, &expr2).unwrap();

        // The metavariables should be unified
        // (either m1 assigned to m2 or vice versa)
    }
}
