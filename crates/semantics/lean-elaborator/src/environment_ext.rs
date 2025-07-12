//! Environment extensions for elaboration
//!
//! This module provides utilities for managing the environment during
//! elaboration, including adding standard library definitions and handling
//! imports.

use lean_kernel::{
    environment::{Declaration, Environment},
    Expr, Level, Name,
};

use crate::error::ElabError;

/// Initialize a basic environment with essential definitions
pub fn init_basic_environment() -> Environment {
    let mut env = Environment::new();

    // Add basic universe levels
    let _ = env.add_universe(Name::mk_simple("u"));
    let _ = env.add_universe(Name::mk_simple("v"));
    let _ = env.add_universe(Name::mk_simple("w"));

    // Add core types
    add_core_types(&mut env);

    // Add basic arithmetic
    add_basic_arithmetic(&mut env);

    env
}

/// Add core types to the environment
fn add_core_types(env: &mut Environment) {
    // Prop : Sort 0
    let prop_decl = Declaration {
        name: Name::mk_simple("Prop"),
        universe_params: vec![],
        ty: Expr::sort(Level::zero()),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(prop_decl);

    // Type : Sort 1
    let type_decl = Declaration {
        name: Name::mk_simple("Type"),
        universe_params: vec![],
        ty: Expr::sort(Level::succ(Level::zero())),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(type_decl);

    // Type* : Sort (1+1)
    let type_star_decl = Declaration {
        name: Name::mk_simple("Type*"),
        universe_params: vec![],
        ty: Expr::sort(Level::succ(Level::succ(Level::zero()))),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(type_star_decl);

    // Bool : Type
    let bool_decl = Declaration {
        name: Name::mk_simple("Bool"),
        universe_params: vec![],
        ty: Expr::const_expr("Type".into(), vec![]),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(bool_decl);

    // true : Bool
    let true_decl = Declaration {
        name: Name::mk_simple("true"),
        universe_params: vec![],
        ty: Expr::const_expr("Bool".into(), vec![]),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(true_decl);

    // false : Bool
    let false_decl = Declaration {
        name: Name::mk_simple("false"),
        universe_params: vec![],
        ty: Expr::const_expr("Bool".into(), vec![]),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(false_decl);

    // Nat : Type
    let nat_decl = Declaration {
        name: Name::mk_simple("Nat"),
        universe_params: vec![],
        ty: Expr::const_expr("Type".into(), vec![]),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(nat_decl);

    // zero : Nat
    let zero_decl = Declaration {
        name: Name::str(Name::mk_simple("Nat"), "zero"),
        universe_params: vec![],
        ty: Expr::const_expr("Nat".into(), vec![]),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(zero_decl);

    // succ : Nat → Nat
    let succ_decl = Declaration {
        name: Name::str(Name::mk_simple("Nat"), "succ"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Nat".into(), vec![]),
            Expr::const_expr("Nat".into(), vec![]),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(succ_decl);

    // String : Type
    let string_decl = Declaration {
        name: Name::mk_simple("String"),
        universe_params: vec![],
        ty: Expr::const_expr("Type".into(), vec![]),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(string_decl);

    // Char : Type
    let char_decl = Declaration {
        name: Name::mk_simple("Char"),
        universe_params: vec![],
        ty: Expr::const_expr("Type".into(), vec![]),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(char_decl);
}

/// Add basic arithmetic operations
fn add_basic_arithmetic(env: &mut Environment) {
    // Add : Nat → Nat → Nat
    let add_decl = Declaration {
        name: Name::str(Name::mk_simple("Nat"), "add"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Nat".into(), vec![]),
            Expr::forall(
                Name::anonymous(),
                Expr::const_expr("Nat".into(), vec![]),
                Expr::const_expr("Nat".into(), vec![]),
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(add_decl);

    // mul : Nat → Nat → Nat
    let mul_decl = Declaration {
        name: Name::str(Name::mk_simple("Nat"), "mul"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Nat".into(), vec![]),
            Expr::forall(
                Name::anonymous(),
                Expr::const_expr("Nat".into(), vec![]),
                Expr::const_expr("Nat".into(), vec![]),
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(mul_decl);

    // sub : Nat → Nat → Nat
    let sub_decl = Declaration {
        name: Name::str(Name::mk_simple("Nat"), "sub"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Nat".into(), vec![]),
            Expr::forall(
                Name::anonymous(),
                Expr::const_expr("Nat".into(), vec![]),
                Expr::const_expr("Nat".into(), vec![]),
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(sub_decl);

    // div : Nat → Nat → Nat
    let div_decl = Declaration {
        name: Name::str(Name::mk_simple("Nat"), "div"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Nat".into(), vec![]),
            Expr::forall(
                Name::anonymous(),
                Expr::const_expr("Nat".into(), vec![]),
                Expr::const_expr("Nat".into(), vec![]),
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(div_decl);

    // mod : Nat → Nat → Nat
    let mod_decl = Declaration {
        name: Name::str(Name::mk_simple("Nat"), "mod"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Nat".into(), vec![]),
            Expr::forall(
                Name::anonymous(),
                Expr::const_expr("Nat".into(), vec![]),
                Expr::const_expr("Nat".into(), vec![]),
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(mod_decl);

    // eq : {α : Type} → α → α → Prop
    let eq_decl = Declaration {
        name: Name::mk_simple("Eq"),
        universe_params: vec![Name::mk_simple("u")],
        ty: Expr::forall(
            Name::mk_simple("α"),
            Expr::const_expr("Type".into(), vec![Level::param(Name::mk_simple("u"))]),
            Expr::forall(
                Name::anonymous(),
                Expr::bvar(0), // α
                Expr::forall(
                    Name::anonymous(),
                    Expr::bvar(1), // α
                    Expr::const_expr("Prop".into(), vec![]),
                    lean_kernel::expr::BinderInfo::Default,
                ),
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Implicit,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(eq_decl);

    // And : Prop → Prop → Prop
    let and_decl = Declaration {
        name: Name::mk_simple("And"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Prop".into(), vec![]),
            Expr::forall(
                Name::anonymous(),
                Expr::const_expr("Prop".into(), vec![]),
                Expr::const_expr("Prop".into(), vec![]),
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(and_decl);

    // Or : Prop → Prop → Prop
    let or_decl = Declaration {
        name: Name::mk_simple("Or"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Prop".into(), vec![]),
            Expr::forall(
                Name::anonymous(),
                Expr::const_expr("Prop".into(), vec![]),
                Expr::const_expr("Prop".into(), vec![]),
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(or_decl);

    // Not : Prop → Prop
    let not_decl = Declaration {
        name: Name::mk_simple("Not"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Prop".into(), vec![]),
            Expr::const_expr("Prop".into(), vec![]),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(not_decl);

    // ite : {α : Type} → Decidable p → α → α → α
    let ite_decl = Declaration {
        name: Name::mk_simple("ite"),
        universe_params: vec![Name::mk_simple("u")],
        ty: Expr::forall(
            Name::mk_simple("α"),
            Expr::const_expr("Type".into(), vec![Level::param(Name::mk_simple("u"))]),
            Expr::forall(
                Name::mk_simple("p"),
                Expr::const_expr("Prop".into(), vec![]),
                Expr::forall(
                    Name::anonymous(),
                    Expr::app(
                        Expr::const_expr("Decidable".into(), vec![]),
                        Expr::bvar(0), // p
                    ),
                    Expr::forall(
                        Name::anonymous(),
                        Expr::bvar(2), // α
                        Expr::forall(
                            Name::anonymous(),
                            Expr::bvar(3), // α
                            Expr::bvar(4), // α
                            lean_kernel::expr::BinderInfo::Default,
                        ),
                        lean_kernel::expr::BinderInfo::Default,
                    ),
                    lean_kernel::expr::BinderInfo::InstImplicit,
                ),
                lean_kernel::expr::BinderInfo::Implicit,
            ),
            lean_kernel::expr::BinderInfo::Implicit,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(ite_decl);

    // Decidable : Prop → Type
    let decidable_decl = Declaration {
        name: Name::mk_simple("Decidable"),
        universe_params: vec![],
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr("Prop".into(), vec![]),
            Expr::const_expr("Type".into(), vec![]),
            lean_kernel::expr::BinderInfo::Default,
        ),
        value: None,
        is_trusted: true,
    };
    let _ = env.add_declaration(decidable_decl);
}

/// Add a user definition to the environment
pub fn add_definition(
    env: &mut Environment,
    name: Name,
    ty: Expr,
    value: Option<Expr>,
    universe_params: Vec<Name>,
) -> Result<(), ElabError> {
    let decl = Declaration {
        name: name.clone(),
        universe_params,
        ty,
        value,
        is_trusted: false,
    };

    env.add_declaration(decl)
        .map_err(ElabError::ElaborationFailed)?;

    Ok(())
}

/// Add a user axiom to the environment
pub fn add_axiom(
    env: &mut Environment,
    name: Name,
    ty: Expr,
    universe_params: Vec<Name>,
) -> Result<(), ElabError> {
    let decl = Declaration {
        name: name.clone(),
        universe_params,
        ty,
        value: None,
        is_trusted: false,
    };

    env.add_declaration(decl)
        .map_err(ElabError::ElaborationFailed)?;

    Ok(())
}

/// Check if a name refers to a constructor
pub fn is_constructor(env: &Environment, name: &Name) -> bool {
    // This is a simplified check - in a real implementation,
    // we'd track constructor information in the environment
    if let Some(_decl) = env.get_declaration(name) {
        // For now, check some common constructor patterns
        let name_str = name.to_string();
        name_str.contains("cons")
            || name_str.contains("nil")
            || name_str == "true"
            || name_str == "false"
            || name_str.contains("zero")
            || name_str.contains("succ")
    } else {
        false
    }
}

/// Check if a name refers to a structure
pub fn is_structure(env: &Environment, name: &Name) -> bool {
    // This is a simplified check - in a real implementation,
    // we'd track structure information in the environment
    if let Some(_decl) = env.get_declaration(name) {
        // For now, assume anything not a constructor might be a structure
        !is_constructor(env, name)
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init_basic_environment() {
        let env = init_basic_environment();

        // Check that basic types exist
        assert!(env.contains(&Name::mk_simple("Prop")));
        assert!(env.contains(&Name::mk_simple("Type")));
        assert!(env.contains(&Name::mk_simple("Bool")));
        assert!(env.contains(&Name::mk_simple("Nat")));
        assert!(env.contains(&Name::mk_simple("String")));

        // Check that basic constructors exist
        assert!(env.contains(&Name::mk_simple("true")));
        assert!(env.contains(&Name::mk_simple("false")));
        assert!(env.contains(&Name::str(Name::mk_simple("Nat"), "zero")));
        assert!(env.contains(&Name::str(Name::mk_simple("Nat"), "succ")));

        // Check that basic operations exist
        assert!(env.contains(&Name::str(Name::mk_simple("Nat"), "add")));
        assert!(env.contains(&Name::mk_simple("Eq")));
        assert!(env.contains(&Name::mk_simple("And")));
        assert!(env.contains(&Name::mk_simple("Or")));
        assert!(env.contains(&Name::mk_simple("Not")));
    }

    #[test]
    fn test_add_definition() {
        let mut env = init_basic_environment();

        // Add a simple definition: identity : {α : Type} → α → α
        let id_ty = Expr::forall(
            Name::mk_simple("α"),
            Expr::const_expr("Type".into(), vec![]),
            Expr::forall(
                Name::mk_simple("x"),
                Expr::bvar(0), // α
                Expr::bvar(1), // α
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Implicit,
        );

        let id_value = Expr::lam(
            Name::mk_simple("α"),
            Expr::const_expr("Type".into(), vec![]),
            Expr::lam(
                Name::mk_simple("x"),
                Expr::bvar(0), // α
                Expr::bvar(0), // x
                lean_kernel::expr::BinderInfo::Default,
            ),
            lean_kernel::expr::BinderInfo::Implicit,
        );

        let result = add_definition(
            &mut env,
            Name::mk_simple("id"),
            id_ty,
            Some(id_value),
            vec![Name::mk_simple("u")],
        );

        assert!(result.is_ok());
        assert!(env.contains(&Name::mk_simple("id")));
    }

    #[test]
    fn test_add_axiom() {
        let mut env = init_basic_environment();

        // Add an axiom: classical : ∀ p : Prop, p ∨ ¬p
        let classical_ty = Expr::forall(
            Name::mk_simple("p"),
            Expr::const_expr("Prop".into(), vec![]),
            Expr::app(
                Expr::app(
                    Expr::const_expr("Or".into(), vec![]),
                    Expr::bvar(0), // p
                ),
                Expr::app(
                    Expr::const_expr("Not".into(), vec![]),
                    Expr::bvar(0), // p
                ),
            ),
            lean_kernel::expr::BinderInfo::Default,
        );

        let result = add_axiom(&mut env, Name::mk_simple("classical"), classical_ty, vec![]);

        assert!(result.is_ok());
        assert!(env.contains(&Name::mk_simple("classical")));
    }

    #[test]
    fn test_constructor_check() {
        let env = init_basic_environment();

        // Test constructor identification
        assert!(is_constructor(&env, &Name::mk_simple("true")));
        assert!(is_constructor(&env, &Name::mk_simple("false")));
        assert!(is_constructor(
            &env,
            &Name::str(Name::mk_simple("Nat"), "zero")
        ));
        assert!(is_constructor(
            &env,
            &Name::str(Name::mk_simple("Nat"), "succ")
        ));

        // Test non-constructors
        assert!(!is_constructor(&env, &Name::mk_simple("Prop")));
        assert!(!is_constructor(&env, &Name::mk_simple("Type")));
        assert!(!is_constructor(
            &env,
            &Name::str(Name::mk_simple("Nat"), "add")
        ));
    }
}
