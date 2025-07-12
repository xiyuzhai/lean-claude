//! Tactic elaboration and proof term synthesis
//!
//! This module implements the tactic system for constructing proof terms.
//! Tactics are programs that construct expressions of given types.

use lean_kernel::{expr::BinderInfo, Expr, Name};
use lean_syn_expr::{Syntax, SyntaxKind};

use crate::{
    context::LocalContext, error::ElabError, metavar::MetavarContext, typeck::TypeChecker,
    ElabState,
};

/// Tactic state during proof elaboration
#[derive(Debug, Clone)]
pub struct TacticState {
    /// Goals to prove
    pub goals: Vec<Goal>,
    /// Local context at this point
    pub lctx: LocalContext,
    /// Current goal index
    pub current_goal: usize,
}

/// A proof goal
#[derive(Debug, Clone)]
pub struct Goal {
    /// Metavariable that represents this goal
    pub mvar: Name,
    /// Type that needs to be proven
    pub target: Expr,
    /// Local hypotheses available for this goal
    pub hypotheses: Vec<Hypothesis>,
}

/// A local hypothesis in a goal
#[derive(Debug, Clone)]
pub struct Hypothesis {
    /// Name of the hypothesis
    pub name: Name,
    /// Type of the hypothesis
    pub ty: Expr,
    /// Optional value (for let-bindings)
    pub value: Option<Expr>,
}

/// Tactic execution result
#[derive(Debug)]
pub enum TacticResult {
    /// Tactic succeeded and produced new goals
    Success(Vec<Goal>),
    /// Tactic succeeded and closed the goal
    Closed,
    /// Tactic failed with an error
    Failed(ElabError),
}

/// Tactic implementation trait
pub trait Tactic {
    fn apply(&self, goal: &Goal, state: &mut ElabState) -> TacticResult;
    fn name(&self) -> &str;
}

impl TacticState {
    pub fn new(target: Expr, lctx: LocalContext, mctx: &mut MetavarContext) -> Self {
        let mvar = mctx.mk_metavar(target.clone(), lctx.clone());
        let mvar_name = if let lean_kernel::expr::ExprKind::MVar(name) = &mvar.kind {
            name.clone()
        } else {
            panic!("mk_metavar should return a metavariable");
        };

        let goal = Goal {
            mvar: mvar_name,
            target,
            hypotheses: vec![],
        };

        Self {
            goals: vec![goal],
            lctx,
            current_goal: 0,
        }
    }

    /// Get the current goal
    pub fn current_goal(&self) -> Option<&Goal> {
        self.goals.get(self.current_goal)
    }

    /// Check if all goals are solved
    pub fn is_complete(&self) -> bool {
        self.goals.is_empty()
    }

    /// Apply a tactic to the current goal
    pub fn apply_tactic(
        &mut self,
        tactic: &dyn Tactic,
        state: &mut ElabState,
    ) -> Result<(), ElabError> {
        if let Some(goal) = self.goals.get(self.current_goal).cloned() {
            match tactic.apply(&goal, state) {
                TacticResult::Success(new_goals) => {
                    // Replace current goal with new goals
                    self.goals.remove(self.current_goal);
                    for (i, new_goal) in new_goals.into_iter().enumerate() {
                        self.goals.insert(self.current_goal + i, new_goal);
                    }
                    Ok(())
                }
                TacticResult::Closed => {
                    // Remove the current goal
                    self.goals.remove(self.current_goal);
                    if self.current_goal >= self.goals.len() && !self.goals.is_empty() {
                        self.current_goal = self.goals.len() - 1;
                    }
                    Ok(())
                }
                TacticResult::Failed(err) => Err(err),
            }
        } else {
            Err(ElabError::ElaborationFailed("No current goal".to_string()))
        }
    }

    /// Switch to a different goal
    pub fn focus_goal(&mut self, index: usize) -> Result<(), ElabError> {
        if index < self.goals.len() {
            self.current_goal = index;
            Ok(())
        } else {
            Err(ElabError::ElaborationFailed(format!(
                "Goal index {} out of range (have {} goals)",
                index,
                self.goals.len()
            )))
        }
    }

    /// Add a new hypothesis to all goals
    pub fn add_hypothesis(&mut self, hyp: Hypothesis) {
        for goal in &mut self.goals {
            goal.hypotheses.push(hyp.clone());
        }
    }
}

/// Basic tactics

/// Exact tactic: proves the goal with a given expression
pub struct ExactTactic {
    pub proof: Expr,
}

impl Tactic for ExactTactic {
    fn apply(&self, goal: &Goal, state: &mut ElabState) -> TacticResult {
        // Check that the proof has the right type
        let mut tc = if let Some(env) = &state.env {
            TypeChecker::with_env(&state.lctx, &mut state.mctx, env)
        } else {
            TypeChecker::new(&state.lctx, &mut state.mctx)
        };

        match tc.check_type(&self.proof, &goal.target) {
            Ok(()) => {
                // Assign the metavariable
                if let Err(e) = state.mctx.assign(goal.mvar.clone(), self.proof.clone()) {
                    TacticResult::Failed(ElabError::ElaborationFailed(e))
                } else {
                    TacticResult::Closed
                }
            }
            Err(e) => TacticResult::Failed(e),
        }
    }

    fn name(&self) -> &str {
        "exact"
    }
}

/// Assumption tactic: proves the goal using a hypothesis
pub struct AssumptionTactic;

impl Tactic for AssumptionTactic {
    fn apply(&self, goal: &Goal, state: &mut ElabState) -> TacticResult {
        // Look for a hypothesis with the same type as the goal
        for hyp in &goal.hypotheses {
            let mut tc = if let Some(env) = &state.env {
                TypeChecker::with_env(&state.lctx, &mut state.mctx, env)
            } else {
                TypeChecker::new(&state.lctx, &mut state.mctx)
            };

            if let Ok(true) = tc.is_def_eq(&hyp.ty, &goal.target) {
                // Use this hypothesis
                let proof = Expr::fvar(hyp.name.clone());
                if let Err(e) = state.mctx.assign(goal.mvar.clone(), proof) {
                    return TacticResult::Failed(ElabError::ElaborationFailed(e));
                } else {
                    return TacticResult::Closed;
                }
            }
        }

        TacticResult::Failed(ElabError::ElaborationFailed(
            "No matching hypothesis found".to_string(),
        ))
    }

    fn name(&self) -> &str {
        "assumption"
    }
}

/// Intro tactic: introduces a lambda or forall
pub struct IntroTactic {
    pub name: Option<Name>,
}

impl Tactic for IntroTactic {
    fn apply(&self, goal: &Goal, state: &mut ElabState) -> TacticResult {
        use lean_kernel::expr::ExprKind;

        match &goal.target.kind {
            ExprKind::Forall(param_name, domain, codomain, _info) => {
                // Introduce a new hypothesis
                let hyp_name = self.name.clone().unwrap_or_else(|| param_name.clone());

                // Create a new goal for the codomain
                let new_target = (**codomain).clone(); // TODO: Proper substitution

                // Create fresh metavariable for the new goal
                let new_mvar = state
                    .mctx
                    .mk_metavar(new_target.clone(), state.lctx.clone());
                let new_mvar_name = if let ExprKind::MVar(name) = &new_mvar.kind {
                    name.clone()
                } else {
                    return TacticResult::Failed(ElabError::ElaborationFailed(
                        "Failed to create metavariable".to_string(),
                    ));
                };

                // Create new hypothesis
                let new_hyp = Hypothesis {
                    name: hyp_name.clone(),
                    ty: (**domain).clone(),
                    value: None,
                };

                // Create new goal with the hypothesis
                let mut new_goal = Goal {
                    mvar: new_mvar_name,
                    target: new_target,
                    hypotheses: goal.hypotheses.clone(),
                };
                new_goal.hypotheses.push(new_hyp);

                // Construct the lambda term
                let lambda = Expr::lam(hyp_name, (**domain).clone(), new_mvar, BinderInfo::Default);

                // Assign the original metavariable
                if let Err(e) = state.mctx.assign(goal.mvar.clone(), lambda) {
                    TacticResult::Failed(ElabError::ElaborationFailed(e))
                } else {
                    TacticResult::Success(vec![new_goal])
                }
            }
            _ => TacticResult::Failed(ElabError::ElaborationFailed(
                "Goal is not a forall type".to_string(),
            )),
        }
    }

    fn name(&self) -> &str {
        "intro"
    }
}

/// Apply tactic: applies a function to the goal
pub struct ApplyTactic {
    pub func: Expr,
}

impl Tactic for ApplyTactic {
    fn apply(&self, goal: &Goal, state: &mut ElabState) -> TacticResult {
        use lean_kernel::expr::ExprKind;

        // Infer the type of the function
        let mut tc = if let Some(env) = &state.env {
            TypeChecker::with_env(&state.lctx, &mut state.mctx, env)
        } else {
            TypeChecker::new(&state.lctx, &mut state.mctx)
        };

        let func_type = match tc.infer_type(&self.func) {
            Ok(ty) => ty,
            Err(e) => return TacticResult::Failed(e),
        };

        // The function type should be a forall
        match &func_type.kind {
            ExprKind::Forall(_param_name, _domain, codomain, _info) => {
                // Check if the codomain unifies with the goal
                if let Ok(true) = tc.is_def_eq(codomain, &goal.target) {
                    // Create a new goal for the domain
                    let new_target = (**_domain).clone();
                    let new_mvar = state
                        .mctx
                        .mk_metavar(new_target.clone(), state.lctx.clone());
                    let new_mvar_name = if let ExprKind::MVar(name) = &new_mvar.kind {
                        name.clone()
                    } else {
                        return TacticResult::Failed(ElabError::ElaborationFailed(
                            "Failed to create metavariable".to_string(),
                        ));
                    };

                    let new_goal = Goal {
                        mvar: new_mvar_name,
                        target: new_target,
                        hypotheses: goal.hypotheses.clone(),
                    };

                    // Apply the function to the metavariable
                    let app = Expr::app(self.func.clone(), new_mvar);

                    // Assign the original metavariable
                    if let Err(e) = state.mctx.assign(goal.mvar.clone(), app) {
                        TacticResult::Failed(ElabError::ElaborationFailed(e))
                    } else {
                        TacticResult::Success(vec![new_goal])
                    }
                } else {
                    TacticResult::Failed(ElabError::ElaborationFailed(
                        "Function codomain does not match goal".to_string(),
                    ))
                }
            }
            _ => {
                // Try direct application if the function type matches the goal
                if let Ok(true) = tc.is_def_eq(&func_type, &goal.target) {
                    // The function itself is the proof
                    if let Err(e) = state.mctx.assign(goal.mvar.clone(), self.func.clone()) {
                        TacticResult::Failed(ElabError::ElaborationFailed(e))
                    } else {
                        TacticResult::Closed
                    }
                } else {
                    TacticResult::Failed(ElabError::ElaborationFailed(
                        "Function type does not match goal and is not a forall".to_string(),
                    ))
                }
            }
        }
    }

    fn name(&self) -> &str {
        "apply"
    }
}

/// Reflexivity tactic: proves x = x
pub struct ReflTactic;

impl Tactic for ReflTactic {
    fn apply(&self, goal: &Goal, state: &mut ElabState) -> TacticResult {
        use lean_kernel::expr::ExprKind;

        // Check if the goal is an equality
        match &goal.target.kind {
            ExprKind::App(eq_app, right) => {
                if let ExprKind::App(eq_const, left) = &eq_app.kind {
                    if let ExprKind::Const(name, _) = &eq_const.kind {
                        if name.to_string() == "Eq" {
                            // This is an equality: Eq left right
                            // Check if left and right are definitionally equal
                            let mut tc = if let Some(env) = &state.env {
                                TypeChecker::with_env(&state.lctx, &mut state.mctx, env)
                            } else {
                                TypeChecker::new(&state.lctx, &mut state.mctx)
                            };

                            if let Ok(true) = tc.is_def_eq(left, right) {
                                // Use Eq.refl
                                let refl = Expr::const_expr("Eq.refl".into(), vec![]);
                                let proof = Expr::app(refl, (**left).clone());

                                if let Err(e) = state.mctx.assign(goal.mvar.clone(), proof) {
                                    TacticResult::Failed(ElabError::ElaborationFailed(e))
                                } else {
                                    TacticResult::Closed
                                }
                            } else {
                                TacticResult::Failed(ElabError::ElaborationFailed(
                                    "Left and right sides are not definitionally equal".to_string(),
                                ))
                            }
                        } else {
                            TacticResult::Failed(ElabError::ElaborationFailed(
                                "Goal is not an equality".to_string(),
                            ))
                        }
                    } else {
                        TacticResult::Failed(ElabError::ElaborationFailed(
                            "Goal is not an equality".to_string(),
                        ))
                    }
                } else {
                    TacticResult::Failed(ElabError::ElaborationFailed(
                        "Goal is not an equality".to_string(),
                    ))
                }
            }
            _ => TacticResult::Failed(ElabError::ElaborationFailed(
                "Goal is not an equality".to_string(),
            )),
        }
    }

    fn name(&self) -> &str {
        "refl"
    }
}

/// Elaborate tactic syntax into tactic applications
pub fn elaborate_tactic(
    syntax: &Syntax,
    state: &mut ElabState,
) -> Result<Box<dyn Tactic>, ElabError> {
    match syntax {
        Syntax::Node(node) => match node.kind {
            SyntaxKind::Exact => {
                if !node.children.is_empty() {
                    // Elaborate the proof expression
                    let proof_syntax = &node.children[0];
                    let proof = elaborate_proof_term(proof_syntax, state)?;
                    Ok(Box::new(ExactTactic { proof }))
                } else {
                    Err(ElabError::InvalidSyntax(
                        "exact tactic requires an argument".to_string(),
                    ))
                }
            }
            SyntaxKind::Assumption => Ok(Box::new(AssumptionTactic)),
            SyntaxKind::Intro => {
                let name = if !node.children.is_empty() {
                    if let Syntax::Atom(atom) = &node.children[0] {
                        Some(Name::mk_simple(atom.value.as_str()))
                    } else {
                        None
                    }
                } else {
                    None
                };
                Ok(Box::new(IntroTactic { name }))
            }
            SyntaxKind::Apply => {
                if !node.children.is_empty() {
                    let func_syntax = &node.children[0];
                    let func = elaborate_proof_term(func_syntax, state)?;
                    Ok(Box::new(ApplyTactic { func }))
                } else {
                    Err(ElabError::InvalidSyntax(
                        "apply tactic requires an argument".to_string(),
                    ))
                }
            }
            SyntaxKind::Rfl => Ok(Box::new(ReflTactic)),
            _ => Err(ElabError::UnsupportedSyntax(node.kind)),
        },
        Syntax::Atom(atom) => match atom.value.as_str() {
            "assumption" => Ok(Box::new(AssumptionTactic)),
            "intro" => Ok(Box::new(IntroTactic { name: None })),
            "refl" => Ok(Box::new(ReflTactic)),
            _ => Err(ElabError::InvalidSyntax(format!(
                "Unknown tactic: {}",
                atom.value.as_str()
            ))),
        },
        _ => Err(ElabError::InvalidSyntax(
            "Invalid tactic syntax".to_string(),
        )),
    }
}

/// Elaborate a proof term (same as regular term elaboration for now)
fn elaborate_proof_term(syntax: &Syntax, state: &mut ElabState) -> Result<Expr, ElabError> {
    // For now, we use the same elaboration as regular terms
    // In a full implementation, proof terms might have special handling
    let mut elaborator = crate::Elaborator::new();
    *elaborator.state_mut() = state.clone();
    elaborator.elaborate(syntax)
}

/// Elaborate a tactic proof block
pub fn elaborate_tactic_proof(
    tactic_syntaxes: &[Syntax],
    goal_type: Expr,
    state: &mut ElabState,
) -> Result<Expr, ElabError> {
    let mut tactic_state = TacticState::new(goal_type, state.lctx.clone(), &mut state.mctx);

    // Apply each tactic in sequence
    for tactic_syntax in tactic_syntaxes {
        let tactic = elaborate_tactic(tactic_syntax, state)?;
        tactic_state.apply_tactic(tactic.as_ref(), state)?;
    }

    // Check if all goals are solved
    if !tactic_state.is_complete() {
        return Err(ElabError::ElaborationFailed(format!(
            "Unsolved goals remaining: {} goals",
            tactic_state.goals.len()
        )));
    }

    // Extract the proof from the first metavariable
    if let Some(first_goal) = tactic_state.goals.first() {
        if let Some(proof) = state.mctx.get_assignment(&first_goal.mvar) {
            Ok(proof.clone())
        } else {
            Err(ElabError::ElaborationFailed(
                "Goal was not assigned a proof".to_string(),
            ))
        }
    } else {
        // All goals were closed, need to get the proof from the original metavariable
        // This is a bit tricky - we need to track the original metavariable
        Err(ElabError::ElaborationFailed(
            "Cannot extract proof from closed goals".to_string(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use lean_kernel::{Level, Name};

    use super::*;
    use crate::environment_ext::init_basic_environment;

    #[test]
    fn test_tactic_state_creation() {
        let mut mctx = MetavarContext::new();
        let lctx = LocalContext::new();
        let target = Expr::const_expr("Prop".into(), vec![]);

        let tactic_state = TacticState::new(target.clone(), lctx, &mut mctx);

        assert_eq!(tactic_state.goals.len(), 1);
        assert_eq!(tactic_state.current_goal, 0);
        assert_eq!(tactic_state.goals[0].target, target);
    }

    #[test]
    fn test_exact_tactic() {
        let mut state = ElabState::with_env(init_basic_environment());

        // Add a hypothesis to the context
        let prop = Expr::const_expr("Prop".into(), vec![]);
        let h_name = Name::mk_simple("h");
        let h_fvar_id = state.lctx.push_local_decl(h_name.clone(), prop.clone());
        let h_fvar = Expr::fvar(h_fvar_id);

        // Goal: Prop (which we can prove with h)
        let goal_type = prop.clone();
        let goal_mvar = state.mctx.mk_metavar(goal_type.clone(), state.lctx.clone());
        let goal_mvar_name = if let lean_kernel::expr::ExprKind::MVar(name) = &goal_mvar.kind {
            name.clone()
        } else {
            panic!("Expected metavariable");
        };

        let goal = Goal {
            mvar: goal_mvar_name.clone(),
            target: goal_type,
            hypotheses: vec![Hypothesis {
                name: h_name.clone(),
                ty: prop.clone(),
                value: None,
            }],
        };

        // Proof: h (the hypothesis)
        let proof = h_fvar;
        let exact_tactic = ExactTactic { proof };

        match exact_tactic.apply(&goal, &mut state) {
            TacticResult::Closed => {
                // Check that the metavariable was assigned
                assert!(state.mctx.is_assigned(&goal_mvar_name));
            }
            _ => panic!("Expected tactic to succeed"),
        }
    }

    #[test]
    fn test_intro_tactic() {
        let mut state = ElabState::with_env(init_basic_environment());

        // Goal: Prop → Prop
        let prop = Expr::const_expr("Prop".into(), vec![]);
        let goal_type = Expr::forall(
            Name::mk_simple("p"),
            prop.clone(),
            prop.clone(),
            BinderInfo::Default,
        );

        let goal_mvar = state.mctx.mk_metavar(goal_type.clone(), state.lctx.clone());
        let goal_mvar_name = if let lean_kernel::expr::ExprKind::MVar(name) = &goal_mvar.kind {
            name.clone()
        } else {
            panic!("Expected metavariable");
        };

        let goal = Goal {
            mvar: goal_mvar_name,
            target: goal_type,
            hypotheses: vec![],
        };

        let intro_tactic = IntroTactic {
            name: Some(Name::mk_simple("h")),
        };

        match intro_tactic.apply(&goal, &mut state) {
            TacticResult::Success(new_goals) => {
                assert_eq!(new_goals.len(), 1);
                assert_eq!(new_goals[0].hypotheses.len(), 1);
                assert_eq!(new_goals[0].hypotheses[0].name.to_string(), "h");
                assert_eq!(new_goals[0].hypotheses[0].ty, prop);
            }
            _ => panic!("Expected tactic to succeed with new goals"),
        }
    }

    #[test]
    fn test_assumption_tactic() {
        let mut state = ElabState::with_env(init_basic_environment());

        let prop = Expr::const_expr("Prop".into(), vec![]);
        let goal_mvar = state.mctx.mk_metavar(prop.clone(), state.lctx.clone());
        let goal_mvar_name = if let lean_kernel::expr::ExprKind::MVar(name) = &goal_mvar.kind {
            name.clone()
        } else {
            panic!("Expected metavariable");
        };

        // Create a goal with a matching hypothesis
        let hyp = Hypothesis {
            name: Name::mk_simple("h"),
            ty: prop.clone(),
            value: None,
        };

        let goal = Goal {
            mvar: goal_mvar_name.clone(),
            target: prop,
            hypotheses: vec![hyp],
        };

        let assumption_tactic = AssumptionTactic;

        match assumption_tactic.apply(&goal, &mut state) {
            TacticResult::Closed => {
                // Check that the metavariable was assigned
                assert!(state.mctx.is_assigned(&goal_mvar_name));
            }
            _ => panic!("Expected tactic to succeed"),
        }
    }

    #[test]
    fn test_tactic_state_goal_management() {
        let mut mctx = MetavarContext::new();
        let lctx = LocalContext::new();
        let target = Expr::const_expr("Prop".into(), vec![]);

        let mut tactic_state = TacticState::new(target, lctx, &mut mctx);

        // Test focus_goal
        assert!(tactic_state.focus_goal(0).is_ok());
        assert!(tactic_state.focus_goal(1).is_err());

        // Test add_hypothesis
        let hyp = Hypothesis {
            name: Name::mk_simple("test"),
            ty: Expr::const_expr("Prop".into(), vec![]),
            value: None,
        };
        tactic_state.add_hypothesis(hyp);

        assert_eq!(tactic_state.goals[0].hypotheses.len(), 1);
        assert_eq!(tactic_state.goals[0].hypotheses[0].name.to_string(), "test");
    }

    #[test]
    fn test_refl_tactic() {
        let mut state = ElabState::with_env(init_basic_environment());

        // Goal: Eq Nat 5 5
        let nat = Expr::const_expr("Nat".into(), vec![]);
        let five = Expr::nat(5);
        let eq_const = Expr::const_expr("Eq".into(), vec![]);
        let eq_five_five = Expr::app(Expr::app(eq_const, five.clone()), five.clone());

        let goal_mvar = state
            .mctx
            .mk_metavar(eq_five_five.clone(), state.lctx.clone());
        let goal_mvar_name = if let lean_kernel::expr::ExprKind::MVar(name) = &goal_mvar.kind {
            name.clone()
        } else {
            panic!("Expected metavariable");
        };

        let goal = Goal {
            mvar: goal_mvar_name.clone(),
            target: eq_five_five,
            hypotheses: vec![],
        };

        let refl_tactic = ReflTactic;

        match refl_tactic.apply(&goal, &mut state) {
            TacticResult::Closed => {
                // Check that the metavariable was assigned
                assert!(state.mctx.is_assigned(&goal_mvar_name));
            }
            _ => panic!("Expected refl tactic to succeed"),
        }
    }
}
