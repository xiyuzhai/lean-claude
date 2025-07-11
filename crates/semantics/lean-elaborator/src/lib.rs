//! Lean 4 elaborator implementation
//!
//! The elaborator is responsible for:
//! - Converting surface syntax to kernel expressions
//! - Type inference and type checking
//! - Implicit argument synthesis
//! - Metavariable management
//! - Instance resolution

pub mod context;
pub mod elab;
pub mod elab_rules;
pub mod error;
pub mod instances;
pub mod metavar;
pub mod patterns;
pub mod typeck;

pub use context::{LevelContext, LocalContext, LocalDecl};
pub use elab::{ElabState, Elaborator};
pub use elab_rules::{ElabRule, ElabRuleAction, ElabRulesRegistry};
pub use error::ElabError;
pub use instances::{Instance, InstanceContext, InstanceResolver};
pub use metavar::{MetavarContext, MetavarDecl};
pub use typeck::{TypeChecker, Unifier};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_elaborator_creation() {
        let _elab = Elaborator::new();
    }
}
