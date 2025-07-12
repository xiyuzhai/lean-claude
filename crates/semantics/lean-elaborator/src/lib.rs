//! Lean 4 elaborator implementation
//!
//! The elaborator is responsible for:
//! - Converting surface syntax to kernel expressions
//! - Type inference and type checking
//! - Implicit argument synthesis
//! - Metavariable management
//! - Instance resolution

pub mod command;
pub mod context;
pub mod elab;
pub mod elab_rules;
pub mod environment_ext;
pub mod error;
pub mod inductive;
pub mod instances;
pub mod metavar;
pub mod module_loader;
pub mod namespace;
pub mod patterns;
pub mod tactics;
pub mod typeck;
pub mod universe;

pub use context::{LevelContext, LocalContext, LocalDecl};
pub use elab::{ElabState, Elaborator};
pub use elab_rules::{ElabRule, ElabRuleAction, ElabRulesRegistry};
pub use environment_ext::{
    add_axiom, add_definition, init_basic_environment, is_constructor, is_structure,
};
pub use error::ElabError;
pub use inductive::{
    add_inductive_to_env, compile_pattern_match, create_list_inductive, create_nat_inductive,
    Constructor, Eliminator, InductiveFamily, InductiveType, Parameter,
};
pub use instances::{Instance, InstanceContext, InstanceResolver};
pub use metavar::{MetavarContext, MetavarDecl};
pub use tactics::{
    elaborate_tactic, elaborate_tactic_proof, Goal, Hypothesis, Tactic, TacticResult, TacticState,
};
pub use typeck::{TypeChecker, Unifier};
pub use universe::{
    compute_pi_universe_level, infer_sort_level, UniverseConstraint, UniverseConstraintSolver,
    UniverseInferenceContext,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_elaborator_creation() {
        let _elab = Elaborator::new();
    }
}
