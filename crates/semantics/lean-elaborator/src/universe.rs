//! Universe level management and inference
//!
//! This module handles universe level checking, inference, and constraints.
//! Universe levels are used to avoid Russell's paradox in the type theory.

use std::collections::{HashMap, HashSet};

use lean_kernel::{Level, Name};

use crate::{error::ElabError, metavar::MetavarContext};

/// Universe level constraints during elaboration
#[derive(Debug, Clone)]
pub enum UniverseConstraint {
    /// u ≤ v (u is less than or equal to v)
    LessEqual { left: Level, right: Level },
    /// u < v (u is strictly less than v)
    StrictLess { left: Level, right: Level },
    /// u = v (u equals v)
    Equal { left: Level, right: Level },
}

/// Universe constraint solver
#[derive(Debug, Default, Clone)]
pub struct UniverseConstraintSolver {
    /// Set of constraints to solve
    constraints: Vec<UniverseConstraint>,
    /// Universe metavariables
    universe_mvars: HashSet<Name>,
    /// Solved universe assignments
    assignments: HashMap<Name, Level>,
}

impl UniverseConstraintSolver {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a universe constraint
    pub fn add_constraint(&mut self, constraint: UniverseConstraint) {
        // Collect universe metavariables from the constraint
        match &constraint {
            UniverseConstraint::LessEqual { left, right }
            | UniverseConstraint::StrictLess { left, right }
            | UniverseConstraint::Equal { left, right } => {
                self.collect_universe_mvars(left);
                self.collect_universe_mvars(right);
            }
        }

        self.constraints.push(constraint);
    }

    /// Collect universe metavariables from a level expression
    fn collect_universe_mvars(&mut self, level: &Level) {
        use lean_kernel::level::LevelKind;

        match &level.kind {
            LevelKind::MVar(name) => {
                self.universe_mvars.insert(name.clone());
            }
            LevelKind::Succ(l) => {
                self.collect_universe_mvars(l);
            }
            LevelKind::Max(l1, l2) | LevelKind::IMax(l1, l2) => {
                self.collect_universe_mvars(l1);
                self.collect_universe_mvars(l2);
            }
            LevelKind::Zero | LevelKind::Param(_) => {}
        }
    }

    /// Solve universe constraints
    pub fn solve(&mut self, mctx: &mut MetavarContext) -> Result<(), ElabError> {
        // Simplified constraint solver
        // In a full implementation, this would use more sophisticated algorithms
        // like the occurs check and normalization

        let mut changed = true;
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 100;

        while changed && iterations < MAX_ITERATIONS {
            changed = false;
            iterations += 1;

            for constraint in &self.constraints.clone() {
                match constraint {
                    UniverseConstraint::Equal { left, right } => {
                        if let Some((name, level)) = self.try_unify_levels(left, right)? {
                            if !self.assignments.contains_key(&name) {
                                self.assignments.insert(name, level);
                                changed = true;
                            }
                        }
                    }
                    UniverseConstraint::LessEqual { left, right } => {
                        // For now, just check if they can be made equal
                        if self.levels_could_be_equal(left, right) {
                            if let Some((name, level)) = self.try_unify_levels(left, right)? {
                                if !self.assignments.contains_key(&name) {
                                    self.assignments.insert(name, level);
                                    changed = true;
                                }
                            }
                        }
                    }
                    UniverseConstraint::StrictLess {
                        left: _left,
                        right: _right,
                    } => {
                        // TODO: Handle strict inequality constraints
                        // For now, we don't solve these
                    }
                }
            }
        }

        if iterations >= MAX_ITERATIONS {
            return Err(ElabError::UniverseLevelError(
                "Universe constraint solver exceeded iteration limit".to_string(),
            ));
        }

        // Apply assignments to metavariable context
        for (name, level) in &self.assignments {
            // TODO: Universe metavariables need to be tracked separately from expression
            // metavariables For now, we skip this step
            let _ = (name, level);
        }

        Ok(())
    }

    /// Try to unify two levels
    fn try_unify_levels(
        &self,
        left: &Level,
        right: &Level,
    ) -> Result<Option<(Name, Level)>, ElabError> {
        use lean_kernel::level::LevelKind;

        match (&left.kind, &right.kind) {
            // Metavar = Level
            (LevelKind::MVar(name), _) if !self.assignments.contains_key(name) => {
                // Check occurs check
                if self.occurs_in_level(name, right) {
                    return Err(ElabError::UniverseLevelError(format!(
                        "Universe level occurs check failed: {name} occurs in {right}"
                    )));
                }
                Ok(Some((name.clone(), right.clone())))
            }
            // Level = Metavar (symmetric case)
            (_, LevelKind::MVar(name)) if !self.assignments.contains_key(name) => {
                // Check occurs check
                if self.occurs_in_level(name, left) {
                    return Err(ElabError::UniverseLevelError(format!(
                        "Universe level occurs check failed: {name} occurs in {left}"
                    )));
                }
                Ok(Some((name.clone(), left.clone())))
            }
            // Already unified cases
            (LevelKind::Zero, LevelKind::Zero) => Ok(None),
            (LevelKind::Param(n1), LevelKind::Param(n2)) if n1 == n2 => Ok(None),
            // Structural unification
            (LevelKind::Succ(l1), LevelKind::Succ(l2)) => self.try_unify_levels(l1, l2),
            (LevelKind::Max(l1a, l1b), LevelKind::Max(l2a, l2b)) => {
                // Try to unify corresponding arguments
                if let Some(assignment) = self.try_unify_levels(l1a, l2a)? {
                    return Ok(Some(assignment));
                }
                self.try_unify_levels(l1b, l2b)
            }
            // Can't unify
            _ => Ok(None),
        }
    }

    /// Check if a universe metavariable occurs in a level
    fn occurs_in_level(&self, mvar: &Name, level: &Level) -> bool {
        use lean_kernel::level::LevelKind;

        match &level.kind {
            LevelKind::MVar(name) => name == mvar,
            LevelKind::Succ(l) => self.occurs_in_level(mvar, l),
            LevelKind::Max(l1, l2) | LevelKind::IMax(l1, l2) => {
                self.occurs_in_level(mvar, l1) || self.occurs_in_level(mvar, l2)
            }
            LevelKind::Zero | LevelKind::Param(_) => false,
        }
    }

    /// Check if two levels could potentially be equal
    fn levels_could_be_equal(&self, left: &Level, right: &Level) -> bool {
        use lean_kernel::level::LevelKind;

        match (&left.kind, &right.kind) {
            // Metavariables can be equal to anything
            (LevelKind::MVar(_), _) | (_, LevelKind::MVar(_)) => true,
            // Structural equality
            (LevelKind::Zero, LevelKind::Zero) => true,
            (LevelKind::Param(n1), LevelKind::Param(n2)) => n1 == n2,
            (LevelKind::Succ(l1), LevelKind::Succ(l2)) => self.levels_could_be_equal(l1, l2),
            (LevelKind::Max(l1a, l1b), LevelKind::Max(l2a, l2b)) => {
                (self.levels_could_be_equal(l1a, l2a) && self.levels_could_be_equal(l1b, l2b))
                    || (self.levels_could_be_equal(l1a, l2b)
                        && self.levels_could_be_equal(l1b, l2a))
            }
            // Different constructors
            _ => false,
        }
    }

    /// Get the assignment for a universe metavariable
    pub fn get_assignment(&self, name: &Name) -> Option<&Level> {
        self.assignments.get(name)
    }

    /// Check if all constraints are satisfied
    pub fn check_constraints(&self) -> Result<(), ElabError> {
        for constraint in &self.constraints {
            match constraint {
                UniverseConstraint::Equal { left, right } => {
                    let left_norm = self.normalize_level(left);
                    let right_norm = self.normalize_level(right);
                    if left_norm != right_norm {
                        return Err(ElabError::UniverseLevelError(format!(
                            "Universe constraint violation: {left} = {right}"
                        )));
                    }
                }
                UniverseConstraint::LessEqual { left, right } => {
                    if !self
                        .check_less_equal(&self.normalize_level(left), &self.normalize_level(right))
                    {
                        return Err(ElabError::UniverseLevelError(format!(
                            "Universe constraint violation: {left} ≤ {right}"
                        )));
                    }
                }
                UniverseConstraint::StrictLess { left, right } => {
                    if !self.check_strict_less(
                        &self.normalize_level(left),
                        &self.normalize_level(right),
                    ) {
                        return Err(ElabError::UniverseLevelError(format!(
                            "Universe constraint violation: {left} < {right}"
                        )));
                    }
                }
            }
        }
        Ok(())
    }

    /// Normalize a level by applying assignments
    fn normalize_level(&self, level: &Level) -> Level {
        use lean_kernel::level::LevelKind;

        match &level.kind {
            LevelKind::MVar(name) => {
                if let Some(assigned_level) = self.assignments.get(name) {
                    self.normalize_level(assigned_level)
                } else {
                    level.clone()
                }
            }
            LevelKind::Succ(l) => {
                let norm_l = self.normalize_level(l);
                if norm_l == **l {
                    level.clone()
                } else {
                    Level::succ(norm_l)
                }
            }
            LevelKind::Max(l1, l2) => {
                let norm_l1 = self.normalize_level(l1);
                let norm_l2 = self.normalize_level(l2);

                // Normalize max expressions
                // max(a, a) = a
                if norm_l1 == norm_l2 {
                    return norm_l1;
                }

                // max(0, a) = max(a, 0) = a if a ≥ 0 (which is always true)
                if let LevelKind::Zero = &norm_l1.kind {
                    return norm_l2;
                }
                if let LevelKind::Zero = &norm_l2.kind {
                    return norm_l1;
                }

                if norm_l1 == **l1 && norm_l2 == **l2 {
                    level.clone()
                } else {
                    Level::max(norm_l1, norm_l2)
                }
            }
            LevelKind::IMax(l1, l2) => {
                let norm_l1 = self.normalize_level(l1);
                let norm_l2 = self.normalize_level(l2);
                if norm_l1 == **l1 && norm_l2 == **l2 {
                    level.clone()
                } else {
                    Level::imax(norm_l1, norm_l2)
                }
            }
            _ => level.clone(),
        }
    }

    /// Check if left ≤ right
    fn check_less_equal(&self, left: &Level, right: &Level) -> bool {
        use lean_kernel::level::LevelKind;

        if left == right {
            return true;
        }

        match (&left.kind, &right.kind) {
            // 0 ≤ anything
            (LevelKind::Zero, _) => true,
            // l ≤ succ(l)
            (_, LevelKind::Succ(r)) => self.check_less_equal(left, r) || left == r.as_ref(),
            // succ(l) ≤ succ(r) iff l ≤ r
            (LevelKind::Succ(l), LevelKind::Succ(r)) => self.check_less_equal(l, r),
            // l ≤ max(l, r) and l ≤ max(r, l)
            (_, LevelKind::Max(r1, r2)) => {
                left == r1.as_ref()
                    || left == r2.as_ref()
                    || self.check_less_equal(left, r1)
                    || self.check_less_equal(left, r2)
            }
            // For parameters and other cases, be conservative
            _ => false,
        }
    }

    /// Check if left < right
    fn check_strict_less(&self, left: &Level, right: &Level) -> bool {
        use lean_kernel::level::LevelKind;

        if left == right {
            return false;
        }

        match (&left.kind, &right.kind) {
            // 0 < succ(anything)
            (LevelKind::Zero, LevelKind::Succ(_)) => true,
            // l < succ(r) if l ≤ r
            (_, LevelKind::Succ(r)) => self.check_less_equal(left, r),
            // succ(l) < succ(r) iff l < r
            (LevelKind::Succ(l), LevelKind::Succ(r)) => self.check_strict_less(l, r),
            // l < max(r1, r2) if l < r1 or l < r2
            (_, LevelKind::Max(r1, r2)) => {
                self.check_strict_less(left, r1) || self.check_strict_less(left, r2)
            }
            // For parameters and other cases, be conservative
            _ => false,
        }
    }
}

/// Universe level inference context
#[derive(Debug, Clone)]
pub struct UniverseInferenceContext {
    /// Constraint solver
    solver: UniverseConstraintSolver,
    /// Next universe metavariable ID
    next_uvar_id: u64,
}

impl UniverseInferenceContext {
    pub fn new() -> Self {
        Self {
            solver: UniverseConstraintSolver::new(),
            next_uvar_id: 0,
        }
    }

    /// Create a fresh universe metavariable
    pub fn mk_universe_mvar(&mut self) -> Level {
        let name = Name::mk_simple(format!("?u.{}", self.next_uvar_id));
        self.next_uvar_id += 1;
        Level::mvar(name)
    }

    /// Add a universe constraint
    pub fn add_constraint(&mut self, constraint: UniverseConstraint) {
        self.solver.add_constraint(constraint);
    }

    /// Solve all universe constraints
    pub fn solve(&mut self, mctx: &mut MetavarContext) -> Result<(), ElabError> {
        self.solver.solve(mctx)
    }

    /// Check if all constraints are satisfied
    pub fn check_constraints(&self) -> Result<(), ElabError> {
        self.solver.check_constraints()
    }

    /// Get the assignment for a universe metavariable
    pub fn get_assignment(&self, name: &Name) -> Option<&Level> {
        self.solver.get_assignment(name)
    }
}

impl Default for UniverseInferenceContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Infer the universe level of a sort expression
pub fn infer_sort_level(
    sort_expr: &lean_kernel::Expr,
    uinfer: &mut UniverseInferenceContext,
) -> Result<Level, ElabError> {
    use lean_kernel::expr::ExprKind;

    match &sort_expr.kind {
        ExprKind::Sort(level) => Ok(level.clone()),
        ExprKind::Const(name, levels) => {
            // For type constants, we need to look up their universe level
            // For now, create a fresh universe metavariable
            let _ = (name, levels);
            Ok(uinfer.mk_universe_mvar())
        }
        _ => {
            // Non-sort expressions need type inference first
            // For now, create a fresh universe metavariable
            Ok(uinfer.mk_universe_mvar())
        }
    }
}

/// Compute the universe level of a Pi type
pub fn compute_pi_universe_level(
    domain_level: &Level,
    codomain_level: &Level,
    uinfer: &mut UniverseInferenceContext,
) -> Level {
    // For dependent function types (Π x : α, β x), the universe level is:
    // imax(level(α), level(β))
    //
    // The imax operation ensures that:
    // - If β : Prop, then the result is level(α)
    // - Otherwise, the result is max(level(α), level(β))

    let result_level = Level::imax(domain_level.clone(), codomain_level.clone());

    // Add constraint that the result level is valid
    uinfer.add_constraint(UniverseConstraint::LessEqual {
        left: domain_level.clone(),
        right: result_level.clone(),
    });
    uinfer.add_constraint(UniverseConstraint::LessEqual {
        left: codomain_level.clone(),
        right: result_level.clone(),
    });

    result_level.normalize()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_universe_mvar_creation() {
        let mut uinfer = UniverseInferenceContext::new();

        let uvar1 = uinfer.mk_universe_mvar();
        let uvar2 = uinfer.mk_universe_mvar();

        // They should be different
        assert_ne!(uvar1, uvar2);

        // They should be metavariables
        assert!(matches!(uvar1.kind, lean_kernel::level::LevelKind::MVar(_)));
        assert!(matches!(uvar2.kind, lean_kernel::level::LevelKind::MVar(_)));
    }

    #[test]
    fn test_constraint_solving_equality() {
        let mut solver = UniverseConstraintSolver::new();
        let mut mctx = MetavarContext::new();

        let uvar = Level::mvar(Name::mk_simple("u"));
        let zero = Level::zero();

        // Add constraint: u = 0
        solver.add_constraint(UniverseConstraint::Equal {
            left: uvar.clone(),
            right: zero.clone(),
        });

        // Solve
        let result = solver.solve(&mut mctx);
        assert!(result.is_ok());

        // Check assignment
        if let lean_kernel::level::LevelKind::MVar(name) = &uvar.kind {
            assert_eq!(solver.get_assignment(name), Some(&zero));
        }
    }

    #[test]
    fn test_constraint_solving_occurs_check() {
        let mut solver = UniverseConstraintSolver::new();
        let mut mctx = MetavarContext::new();

        let uvar = Level::mvar(Name::mk_simple("u"));
        let succ_uvar = Level::succ(uvar.clone());

        // Add constraint: u = succ(u) - should fail occurs check
        solver.add_constraint(UniverseConstraint::Equal {
            left: uvar,
            right: succ_uvar,
        });

        // Solve - should fail
        let result = solver.solve(&mut mctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_level_normalization() {
        let solver = UniverseConstraintSolver::new();

        // Test basic normalization
        let zero = Level::zero();
        let norm_zero = solver.normalize_level(&zero);
        assert_eq!(zero, norm_zero);

        // Test max normalization
        let max_level = Level::max(Level::zero(), Level::zero());
        let norm_max = solver.normalize_level(&max_level);
        // max(0, 0) should normalize to 0
        assert_eq!(norm_max, Level::zero());
    }

    #[test]
    fn test_less_equal_check() {
        let solver = UniverseConstraintSolver::new();

        // 0 ≤ 0
        assert!(solver.check_less_equal(&Level::zero(), &Level::zero()));

        // 0 ≤ succ(0)
        assert!(solver.check_less_equal(&Level::zero(), &Level::succ(Level::zero())));

        // succ(0) ≰ 0
        assert!(!solver.check_less_equal(&Level::succ(Level::zero()), &Level::zero()));

        // 0 ≤ max(0, succ(0))
        assert!(solver.check_less_equal(
            &Level::zero(),
            &Level::max(Level::zero(), Level::succ(Level::zero()))
        ));
    }

    #[test]
    fn test_strict_less_check() {
        let solver = UniverseConstraintSolver::new();

        // 0 ≮ 0
        assert!(!solver.check_strict_less(&Level::zero(), &Level::zero()));

        // 0 < succ(0)
        assert!(solver.check_strict_less(&Level::zero(), &Level::succ(Level::zero())));

        // succ(0) ≮ 0
        assert!(!solver.check_strict_less(&Level::succ(Level::zero()), &Level::zero()));
    }

    #[test]
    fn test_pi_universe_computation() {
        let mut uinfer = UniverseInferenceContext::new();

        let domain_level = Level::zero();
        let codomain_level = Level::succ(Level::zero());

        let pi_level = compute_pi_universe_level(&domain_level, &codomain_level, &mut uinfer);

        // For Π x : Type₀, Type₁, the level should be imax(0, 1) = 1
        let expected = Level::imax(domain_level, codomain_level).normalize();
        assert_eq!(pi_level, expected);
    }

    #[test]
    fn test_constraint_violation_detection() {
        let mut solver = UniverseConstraintSolver::new();

        // Add contradictory constraints: 0 = succ(0)
        solver.add_constraint(UniverseConstraint::Equal {
            left: Level::zero(),
            right: Level::succ(Level::zero()),
        });

        // Check constraints - should fail
        let result = solver.check_constraints();
        assert!(result.is_err());
    }
}
