//! Instance resolution for type classes
//!
//! This module implements the type class resolution mechanism,
//! which automatically finds appropriate instances for implicit instance
//! arguments.

use std::collections::HashMap;

use lean_kernel::{Expr, Name};

use crate::{
    context::LocalContext, error::ElabError, metavar::MetavarContext, typeck::TypeChecker,
};

/// Instance candidate
#[derive(Debug, Clone)]
pub struct Instance {
    /// Name of the instance
    pub name: Name,
    /// Type of the instance
    pub ty: Expr,
    /// Priority for resolution (higher = preferred)
    pub priority: u32,
}

/// Instance resolution context
#[derive(Debug, Default)]
pub struct InstanceContext {
    /// Available instances, indexed by type class name
    instances: HashMap<Name, Vec<Instance>>,
    /// Instance search depth limit
    max_depth: usize,
}

impl InstanceContext {
    pub fn new() -> Self {
        Self {
            instances: HashMap::new(),
            max_depth: 32, // Default depth limit
        }
    }

    /// Add an instance to the context
    pub fn add_instance(&mut self, instance: Instance) {
        // Extract the type class name from the instance type
        if let Some(class_name) = self.extract_class_name(&instance.ty) {
            self.instances.entry(class_name).or_default().push(instance);
        }
    }

    /// Remove all instances (for testing)
    pub fn clear(&mut self) {
        self.instances.clear();
    }

    /// Extract the type class name from an instance type
    /// For example, from `Add Nat` extract `Add`
    #[allow(clippy::only_used_in_recursion)]
    fn extract_class_name(&self, ty: &Expr) -> Option<Name> {
        use lean_kernel::expr::ExprKind;

        match &ty.kind {
            // Direct type class: `Add`
            ExprKind::Const(name, _) => Some(name.clone()),
            // Applied type class: `Add Nat`
            ExprKind::App(f, _) => self.extract_class_name(f),
            // Forall type: `∀ (α : Type), Add α` -> look at the body
            ExprKind::Forall(_, _, body, _) => self.extract_class_name(body),
            _ => None,
        }
    }

    /// Find instances for a given type
    pub fn find_instances(&self, target_ty: &Expr) -> Vec<&Instance> {
        if let Some(class_name) = self.extract_class_name(target_ty) {
            self.instances
                .get(&class_name)
                .map(|instances| instances.iter().collect())
                .unwrap_or_default()
        } else {
            Vec::new()
        }
    }
}

/// Instance resolver
pub struct InstanceResolver<'a> {
    /// Instance context
    inst_ctx: &'a InstanceContext,
    /// Local context for type checking
    lctx: &'a LocalContext,
    /// Metavariable context
    mctx: &'a mut MetavarContext,
    /// Current search depth
    depth: usize,
}

impl<'a> InstanceResolver<'a> {
    pub fn new(
        inst_ctx: &'a InstanceContext,
        lctx: &'a LocalContext,
        mctx: &'a mut MetavarContext,
    ) -> Self {
        Self {
            inst_ctx,
            lctx,
            mctx,
            depth: 0,
        }
    }

    /// Resolve an instance for the given type
    /// Returns the instance expression if found
    pub fn resolve_instance(&mut self, target_ty: &Expr) -> Result<Option<Expr>, ElabError> {
        if self.depth >= self.inst_ctx.max_depth {
            return Ok(None); // Depth limit reached
        }

        self.depth += 1;
        let result = self.resolve_instance_core(target_ty);
        self.depth -= 1;

        result
    }

    fn resolve_instance_core(&mut self, target_ty: &Expr) -> Result<Option<Expr>, ElabError> {
        // Find candidate instances
        let candidates = self.inst_ctx.find_instances(target_ty);

        if candidates.is_empty() {
            return Ok(None);
        }

        // Try each candidate in priority order
        let mut sorted_candidates = candidates;
        sorted_candidates.sort_by(|a, b| b.priority.cmp(&a.priority));

        for candidate in sorted_candidates {
            if let Ok(Some(instance_expr)) = self.try_candidate(candidate, target_ty) {
                return Ok(Some(instance_expr));
            }
        }

        Ok(None)
    }

    /// Try to use a candidate instance
    fn try_candidate(
        &mut self,
        candidate: &Instance,
        target_ty: &Expr,
    ) -> Result<Option<Expr>, ElabError> {
        // Create a type checker for unification
        let mut tc = TypeChecker::new(self.lctx, self.mctx);

        // Check if the candidate type can be unified with the target type
        // This is a simplified version - in practice, we'd need to handle
        // higher-order unification and recursive instance search

        // For now, just check if they're definitionally equal
        if tc.is_def_eq(&candidate.ty, target_ty)? {
            // Create the instance expression
            // This would typically be a constant reference or application
            let instance_expr = Expr::const_expr(candidate.name.clone(), vec![]);
            Ok(Some(instance_expr))
        } else {
            Ok(None)
        }
    }
}

/// Auto-implicit argument handler
/// This integrates instance resolution with the elaborator
pub fn resolve_auto_implicit(
    target_ty: &Expr,
    inst_ctx: &InstanceContext,
    lctx: &LocalContext,
    mctx: &mut MetavarContext,
) -> Result<Option<Expr>, ElabError> {
    let mut resolver = InstanceResolver::new(inst_ctx, lctx, mctx);
    resolver.resolve_instance(target_ty)
}

#[cfg(test)]
mod tests {
    use lean_kernel::Name;

    use super::*;

    #[test]
    fn test_instance_context_creation() {
        let ctx = InstanceContext::new();
        assert_eq!(ctx.instances.len(), 0);
    }

    #[test]
    fn test_add_instance() {
        let mut ctx = InstanceContext::new();

        // Create a simple instance: `Add Nat`
        let add_nat = Instance {
            name: Name::mk_simple("Add.Nat"),
            ty: Expr::app(
                Expr::const_expr("Add".into(), vec![]),
                Expr::const_expr("Nat".into(), vec![]),
            ),
            priority: 100,
        };

        ctx.add_instance(add_nat);

        // Check that it was added
        let add_name = Name::mk_simple("Add");
        assert!(ctx.instances.contains_key(&add_name));
        assert_eq!(ctx.instances[&add_name].len(), 1);
    }

    #[test]
    fn test_extract_class_name() {
        let ctx = InstanceContext::new();

        // Test direct class name
        let add_const = Expr::const_expr("Add".into(), vec![]);
        assert_eq!(
            ctx.extract_class_name(&add_const),
            Some(Name::mk_simple("Add"))
        );

        // Test applied class name
        let add_nat = Expr::app(
            Expr::const_expr("Add".into(), vec![]),
            Expr::const_expr("Nat".into(), vec![]),
        );
        assert_eq!(
            ctx.extract_class_name(&add_nat),
            Some(Name::mk_simple("Add"))
        );
    }

    #[test]
    fn test_find_instances() {
        let mut ctx = InstanceContext::new();

        // Add an Add Nat instance
        let add_nat = Instance {
            name: Name::mk_simple("Add.Nat"),
            ty: Expr::app(
                Expr::const_expr("Add".into(), vec![]),
                Expr::const_expr("Nat".into(), vec![]),
            ),
            priority: 100,
        };

        ctx.add_instance(add_nat);

        // Search for Add instances
        let add_ty = Expr::const_expr("Add".into(), vec![]);
        let instances = ctx.find_instances(&add_ty);
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].name.to_string(), "Add.Nat");
    }

    #[test]
    fn test_instance_resolution() {
        let mut ctx = InstanceContext::new();
        let lctx = LocalContext::new();
        let mut mctx = MetavarContext::new();

        // Add an Add Nat instance
        let add_nat_ty = Expr::app(
            Expr::const_expr("Add".into(), vec![]),
            Expr::const_expr("Nat".into(), vec![]),
        );
        let add_nat = Instance {
            name: Name::mk_simple("Add.Nat"),
            ty: add_nat_ty.clone(),
            priority: 100,
        };

        ctx.add_instance(add_nat);

        // Try to resolve Add Nat
        let mut resolver = InstanceResolver::new(&ctx, &lctx, &mut mctx);
        let result = resolver.resolve_instance(&add_nat_ty).unwrap();

        assert!(result.is_some());
        let instance_expr = result.unwrap();

        // Should be the Add.Nat constant
        match &instance_expr.kind {
            lean_kernel::expr::ExprKind::Const(name, _) => {
                assert_eq!(name.to_string(), "Add.Nat");
            }
            _ => panic!("Expected constant expression"),
        }
    }
}
