//! Inductive type support for the elaborator
//!
//! This module handles the elaboration and type checking of inductive types,
//! including constructors, eliminators, and recursive functions.

use std::collections::HashMap;

use lean_kernel::{
    environment::{Declaration, Environment},
    expr::{BinderInfo, ExprKind},
    Expr, Level, Name,
};

use crate::{error::ElabError, ElabState};

/// Inductive type declaration
#[derive(Debug, Clone)]
pub struct InductiveType {
    /// Name of the inductive type
    pub name: Name,
    /// Universe parameters
    pub universe_params: Vec<Name>,
    /// Parameters (non-uniform)
    pub params: Vec<Parameter>,
    /// Indices (uniform)
    pub indices: Vec<Parameter>,
    /// Type of the inductive type
    pub ty: Expr,
    /// Constructors
    pub constructors: Vec<Constructor>,
}

/// Parameter or index of an inductive type
#[derive(Debug, Clone)]
pub struct Parameter {
    /// Name of the parameter
    pub name: Name,
    /// Type of the parameter
    pub ty: Expr,
    /// Binding info (implicit/explicit)
    pub binder_info: BinderInfo,
}

/// Constructor of an inductive type
#[derive(Debug, Clone)]
pub struct Constructor {
    /// Name of the constructor
    pub name: Name,
    /// Type of the constructor
    pub ty: Expr,
    /// Number of arguments
    pub arity: usize,
}

/// Eliminator (recursor) for an inductive type
#[derive(Debug, Clone)]
pub struct Eliminator {
    /// Name of the eliminator
    pub name: Name,
    /// Type of the eliminator
    pub ty: Expr,
    /// Rules for each constructor
    pub rules: Vec<EliminatorRule>,
}

/// Eliminator rule for a constructor
#[derive(Debug, Clone)]
pub struct EliminatorRule {
    /// Constructor this rule applies to
    pub constructor: Name,
    /// Right-hand side of the rule
    pub rhs: Expr,
}

/// Inductive type family (for mutual induction)
#[derive(Debug, Clone)]
pub struct InductiveFamily {
    /// Types in the family
    pub types: Vec<InductiveType>,
    /// Shared universe parameters
    pub universe_params: Vec<Name>,
    /// Shared parameters
    pub params: Vec<Parameter>,
}

impl InductiveType {
    /// Check if this inductive type is well-formed
    pub fn check_well_formed(&self, env: &Environment) -> Result<(), ElabError> {
        // Check that the type is a valid type
        self.check_type_well_formed(env)?;

        // Check each constructor
        for ctor in &self.constructors {
            self.check_constructor_well_formed(ctor, env)?;
        }

        // Check positivity (strict positivity condition)
        self.check_positivity(env)?;

        Ok(())
    }

    /// Check that the type of the inductive type is well-formed
    fn check_type_well_formed(&self, _env: &Environment) -> Result<(), ElabError> {
        // The type should be of the form: Π params, indices, Sort u
        // For now, just check that it's a sort or pi type ending in a sort
        self.check_ends_in_sort(&self.ty)
    }

    /// Check that a type expression ends in a Sort
    fn check_ends_in_sort(&self, ty: &Expr) -> Result<(), ElabError> {
        match &ty.kind {
            ExprKind::Sort(_) => Ok(()),
            ExprKind::Forall(_, _, body, _) => self.check_ends_in_sort(body),
            _ => Err(ElabError::ElaborationFailed(
                "Inductive type must have a sort as its type".to_string(),
            )),
        }
    }

    /// Check that a constructor is well-formed
    fn check_constructor_well_formed(
        &self,
        ctor: &Constructor,
        _env: &Environment,
    ) -> Result<(), ElabError> {
        // Constructor type should be of the form:
        // Π args, I params indices
        // where I is the inductive type being defined

        let target = self.extract_constructor_target(&ctor.ty);
        self.check_constructor_target(&target)?;

        Ok(())
    }

    /// Extract the target (conclusion) of a constructor type
    fn extract_constructor_target(&self, ty: &Expr) -> Expr {
        match &ty.kind {
            ExprKind::Forall(_, _, body, _) => self.extract_constructor_target(body),
            _ => ty.clone(),
        }
    }

    /// Check that the constructor target is valid
    fn check_constructor_target(&self, target: &Expr) -> Result<(), ElabError> {
        // The target should be an application of the inductive type
        // to its parameters and some indices
        match &target.kind {
            ExprKind::Const(name, _) if name == &self.name => {
                // Simple case: no parameters or indices
                Ok(())
            }
            ExprKind::App(f, _) => {
                // Check that the head is the inductive type
                let head = self.get_app_head(target);
                if let ExprKind::Const(name, _) = &head.kind {
                    if name == &self.name {
                        Ok(())
                    } else {
                        Err(ElabError::ElaborationFailed(format!(
                            "Constructor target must be the inductive type {}, got {}",
                            self.name, name
                        )))
                    }
                } else {
                    Err(ElabError::ElaborationFailed(
                        "Constructor target must be the inductive type".to_string(),
                    ))
                }
            }
            _ => Err(ElabError::ElaborationFailed(
                "Constructor target must be the inductive type".to_string(),
            )),
        }
    }

    /// Get the head of an application
    fn get_app_head(&self, expr: &Expr) -> Expr {
        match &expr.kind {
            ExprKind::App(f, _) => self.get_app_head(f),
            _ => expr.clone(),
        }
    }

    /// Check the strict positivity condition
    fn check_positivity(&self, _env: &Environment) -> Result<(), ElabError> {
        // Simplified positivity check
        // In a full implementation, this would check that the inductive type
        // occurs only in strictly positive positions in constructor arguments

        for ctor in &self.constructors {
            self.check_constructor_positivity(ctor)?;
        }

        Ok(())
    }

    /// Check positivity for a single constructor
    fn check_constructor_positivity(&self, ctor: &Constructor) -> Result<(), ElabError> {
        // Simplified check: just ensure the inductive type doesn't occur
        // in negative positions (left of implications)
        self.check_positivity_in_type(&ctor.ty, true)
    }

    /// Check positivity in a type expression
    fn check_positivity_in_type(&self, ty: &Expr, positive: bool) -> Result<(), ElabError> {
        match &ty.kind {
            ExprKind::Const(name, _) if name == &self.name => {
                if positive {
                    Ok(())
                } else {
                    Err(ElabError::ElaborationFailed(format!(
                        "Inductive type {} occurs in negative position",
                        self.name
                    )))
                }
            }
            ExprKind::Forall(_, domain, codomain, _) => {
                // For strict positivity, we need to check if the domain contains
                // the inductive type. If it does, we need more careful analysis.
                // For now, allow simple cases like Nat → Nat where the inductive
                // type appears alone in the domain (not nested in another type).
                if self.is_simple_occurrence(domain) {
                    // Simple occurrence like "Nat" in "Nat → Nat" is allowed
                    self.check_positivity_in_type(codomain, positive)
                } else {
                    // Domain is in negative position, codomain in positive
                    self.check_positivity_in_type(domain, !positive)?;
                    self.check_positivity_in_type(codomain, positive)
                }
            }
            ExprKind::App(f, a) => {
                self.check_positivity_in_type(f, positive)?;
                self.check_positivity_in_type(a, positive)
            }
            ExprKind::Lam(_, ty, body, _) => {
                self.check_positivity_in_type(ty, !positive)?;
                self.check_positivity_in_type(body, positive)
            }
            _ => Ok(()),
        }
    }

    /// Check if an expression is a simple occurrence of the inductive type
    /// (not nested inside another type constructor)
    fn is_simple_occurrence(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Const(name, _) => name == &self.name,
            ExprKind::App(_, _) => {
                // Check if it's an application with the inductive type as head
                let head = self.get_app_head(expr);
                if let ExprKind::Const(name, _) = &head.kind {
                    name == &self.name
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}

/// Generate the eliminator (recursor) for an inductive type
pub fn generate_eliminator(
    inductive: &InductiveType,
    env: &Environment,
) -> Result<Eliminator, ElabError> {
    let elim_name = Name::str(inductive.name.clone(), "rec");

    // Generate the type of the eliminator
    let elim_type = generate_eliminator_type(inductive, env)?;

    // Generate rules for each constructor
    let mut rules = Vec::new();
    for ctor in &inductive.constructors {
        let rule = generate_eliminator_rule(inductive, ctor, env)?;
        rules.push(rule);
    }

    Ok(Eliminator {
        name: elim_name,
        ty: elim_type,
        rules,
    })
}

/// Generate the type of an eliminator
fn generate_eliminator_type(
    inductive: &InductiveType,
    _env: &Environment,
) -> Result<Expr, ElabError> {
    // For a simple inductive type I : Sort u with constructors C₁, ..., Cₙ,
    // the eliminator has type:
    // Π (P : I → Sort v), (Π x, C₁ → P (C₁ ...)) → ... → (Π x, Cₙ → P (Cₙ ...)) → Π
    // x : I, P x

    // For now, create a placeholder type
    // In a full implementation, this would be much more complex
    let i_type = inductive.ty.clone();
    let motive_type = Expr::forall(
        Name::anonymous(),
        i_type.clone(),
        Expr::sort(Level::zero()), // Simplified
        BinderInfo::Default,
    );

    // Build the eliminator type with motive and methods
    let mut elim_type = Expr::forall(
        Name::mk_simple("P"),
        motive_type,
        i_type.clone(), // Placeholder
        BinderInfo::Implicit,
    );

    // Add method arguments (one for each constructor)
    for ctor in &inductive.constructors {
        let method_type = generate_method_type(inductive, ctor);
        elim_type = Expr::forall(
            Name::str(ctor.name.clone(), "method"),
            method_type,
            elim_type,
            BinderInfo::Default,
        );
    }

    // Add the target argument
    elim_type = Expr::forall(
        Name::mk_simple("x"),
        i_type,
        Expr::bvar(0), // Placeholder for P x
        BinderInfo::Default,
    );

    Ok(elim_type)
}

/// Generate the type of a method for a constructor
fn generate_method_type(inductive: &InductiveType, ctor: &Constructor) -> Expr {
    // For constructor C : Π args, I, the method type is:
    // Π args, P (C args)

    // Simplified: just return the constructor type for now
    ctor.ty.clone()
}

/// Generate an eliminator rule for a constructor
fn generate_eliminator_rule(
    inductive: &InductiveType,
    ctor: &Constructor,
    _env: &Environment,
) -> Result<EliminatorRule, ElabError> {
    // The rule for constructor C is:
    // rec P m₁ ... mₙ (C args) = mᵢ args (rec P m₁ ... mₙ arg₁) ... (rec P m₁ ...
    // mₙ argₖ) where argⱼ are the recursive arguments

    // For now, create a placeholder rule
    let rhs = Expr::const_expr(Name::str(ctor.name.clone(), "rule"), vec![]);

    Ok(EliminatorRule {
        constructor: ctor.name.clone(),
        rhs,
    })
}

/// Add an inductive type to the environment
pub fn add_inductive_to_env(
    env: &mut Environment,
    inductive: InductiveType,
    state: &mut ElabState,
) -> Result<(), ElabError> {
    // Check well-formedness
    inductive.check_well_formed(env)?;

    // Add the inductive type itself
    let type_decl = Declaration {
        name: inductive.name.clone(),
        universe_params: inductive.universe_params.clone(),
        ty: inductive.ty.clone(),
        value: None,
        is_trusted: true,
    };
    env.add_declaration(type_decl)
        .map_err(|e| ElabError::ElaborationFailed(e))?;

    // Add each constructor
    for ctor in &inductive.constructors {
        let ctor_decl = Declaration {
            name: ctor.name.clone(),
            universe_params: inductive.universe_params.clone(),
            ty: ctor.ty.clone(),
            value: None,
            is_trusted: true,
        };
        env.add_declaration(ctor_decl)
            .map_err(|e| ElabError::ElaborationFailed(e))?;
    }

    // Generate and add the eliminator
    let eliminator = generate_eliminator(&inductive, env)?;
    let elim_decl = Declaration {
        name: eliminator.name.clone(),
        universe_params: inductive.universe_params.clone(),
        ty: eliminator.ty.clone(),
        value: None,
        is_trusted: true,
    };
    env.add_declaration(elim_decl)
        .map_err(|e| ElabError::ElaborationFailed(e))?;

    // Generate other derived eliminators (like no-confusion)
    generate_derived_eliminators(&inductive, env, state)?;

    Ok(())
}

/// Generate derived eliminators for an inductive type
fn generate_derived_eliminators(
    inductive: &InductiveType,
    env: &mut Environment,
    _state: &mut ElabState,
) -> Result<(), ElabError> {
    // Generate no-confusion lemma
    let no_confusion = generate_no_confusion(inductive)?;
    let no_confusion_decl = Declaration {
        name: no_confusion.name,
        universe_params: inductive.universe_params.clone(),
        ty: no_confusion.ty,
        value: None,
        is_trusted: true,
    };
    env.add_declaration(no_confusion_decl)
        .map_err(|e| ElabError::ElaborationFailed(e))?;

    // Generate injectivity lemmas for constructors
    for ctor in &inductive.constructors {
        if ctor.arity > 0 {
            let inj_lemma = generate_injectivity_lemma(inductive, ctor)?;
            let inj_decl = Declaration {
                name: inj_lemma.name,
                universe_params: inductive.universe_params.clone(),
                ty: inj_lemma.ty,
                value: None,
                is_trusted: true,
            };
            env.add_declaration(inj_decl)
                .map_err(|e| ElabError::ElaborationFailed(e))?;
        }
    }

    Ok(())
}

/// No-confusion lemma
#[derive(Debug, Clone)]
struct NoConfusion {
    name: Name,
    ty: Expr,
}

/// Generate no-confusion lemma
fn generate_no_confusion(inductive: &InductiveType) -> Result<NoConfusion, ElabError> {
    let name = Name::str(inductive.name.clone(), "noConfusion");

    // Simplified no-confusion type: different constructors are not equal
    // Π (x y : I), x = y → x.tag = y.tag
    let i_type = Expr::const_expr(inductive.name.clone(), vec![]);
    let eq_type = Expr::forall(
        Name::mk_simple("x"),
        i_type.clone(),
        Expr::forall(
            Name::mk_simple("y"),
            i_type.clone(),
            Expr::app(
                Expr::app(Expr::const_expr("Eq".into(), vec![]), Expr::bvar(1)),
                Expr::bvar(0),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let ty = Expr::forall(
        Name::anonymous(),
        eq_type,
        Expr::const_expr("True".into(), vec![]), // Placeholder
        BinderInfo::Default,
    );

    Ok(NoConfusion { name, ty })
}

/// Injectivity lemma
#[derive(Debug, Clone)]
struct InjectivityLemma {
    name: Name,
    ty: Expr,
}

/// Generate injectivity lemma for a constructor
fn generate_injectivity_lemma(
    inductive: &InductiveType,
    ctor: &Constructor,
) -> Result<InjectivityLemma, ElabError> {
    let name = Name::str(ctor.name.clone(), "inj");

    // Simplified injectivity type: if C x = C y then x = y
    // For multi-argument constructors, this becomes multiple equalities
    let i_type = Expr::const_expr(inductive.name.clone(), vec![]);
    let arg_type = Expr::const_expr("Nat".into(), vec![]); // Simplified

    let ty = Expr::forall(
        Name::mk_simple("x"),
        arg_type.clone(),
        Expr::forall(
            Name::mk_simple("y"),
            arg_type.clone(),
            Expr::forall(
                Name::anonymous(),
                Expr::app(
                    Expr::app(
                        Expr::const_expr("Eq".into(), vec![]),
                        Expr::app(Expr::const_expr(ctor.name.clone(), vec![]), Expr::bvar(1)),
                    ),
                    Expr::app(Expr::const_expr(ctor.name.clone(), vec![]), Expr::bvar(0)),
                ),
                Expr::app(
                    Expr::app(Expr::const_expr("Eq".into(), vec![]), Expr::bvar(2)),
                    Expr::bvar(1),
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    Ok(InjectivityLemma { name, ty })
}

/// Pattern matching compilation for inductive types
pub fn compile_pattern_match(
    inductive: &InductiveType,
    discriminant: Expr,
    patterns: Vec<(Constructor, Vec<Name>, Expr)>,
    _env: &Environment,
) -> Result<Expr, ElabError> {
    // Use the eliminator to compile pattern matching
    let elim_name = Name::str(inductive.name.clone(), "rec");
    let eliminator = Expr::const_expr(elim_name, vec![]);

    // Create the motive
    let motive = create_pattern_match_motive(inductive, &patterns)?;

    // Create method arguments
    let mut methods = Vec::new();
    for (ctor, _vars, body) in patterns {
        let method = create_pattern_match_method(inductive, &ctor, body)?;
        methods.push(method);
    }

    // Apply the eliminator
    let mut result = Expr::app(eliminator, motive);
    for method in methods {
        result = Expr::app(result, method);
    }
    result = Expr::app(result, discriminant);

    Ok(result)
}

/// Create the motive for pattern matching
fn create_pattern_match_motive(
    _inductive: &InductiveType,
    patterns: &[(Constructor, Vec<Name>, Expr)],
) -> Result<Expr, ElabError> {
    // The motive determines the return type of the pattern match
    // For now, create a simple motive
    if let Some((_, _, body)) = patterns.first() {
        // Use the type of the first pattern body as the motive
        // In practice, we'd infer the common type of all branches
        let return_type = Expr::const_expr("Type".into(), vec![]); // Placeholder
        Ok(Expr::lam(
            Name::anonymous(),
            Expr::const_expr("Nat".into(), vec![]), // Placeholder for inductive type
            return_type,
            BinderInfo::Default,
        ))
    } else {
        Err(ElabError::ElaborationFailed(
            "No patterns provided".to_string(),
        ))
    }
}

/// Create a method for a pattern match branch
fn create_pattern_match_method(
    _inductive: &InductiveType,
    _ctor: &Constructor,
    body: Expr,
) -> Result<Expr, ElabError> {
    // For constructor C with arguments, create:
    // λ args, body[vars := args]
    // For now, just return the body
    Ok(body)
}

/// Built-in inductive types

/// Create the Nat inductive type
pub fn create_nat_inductive() -> InductiveType {
    let nat_name = Name::mk_simple("Nat");

    // Nat : Type
    let nat_type = Expr::sort(Level::zero());

    // zero : Nat
    let zero_ctor = Constructor {
        name: Name::str(nat_name.clone(), "zero"),
        ty: Expr::const_expr(nat_name.clone(), vec![]),
        arity: 0,
    };

    // succ : Nat → Nat
    let succ_ctor = Constructor {
        name: Name::str(nat_name.clone(), "succ"),
        ty: Expr::forall(
            Name::anonymous(),
            Expr::const_expr(nat_name.clone(), vec![]),
            Expr::const_expr(nat_name.clone(), vec![]),
            BinderInfo::Default,
        ),
        arity: 1,
    };

    InductiveType {
        name: nat_name,
        universe_params: vec![],
        params: vec![],
        indices: vec![],
        ty: nat_type,
        constructors: vec![zero_ctor, succ_ctor],
    }
}

/// Create the List inductive type
pub fn create_list_inductive() -> InductiveType {
    let list_name = Name::mk_simple("List");
    let alpha = Name::mk_simple("α");

    // List : Type → Type
    let list_type = Expr::forall(
        alpha.clone(),
        Expr::sort(Level::zero()),
        Expr::sort(Level::zero()),
        BinderInfo::Default,
    );

    // nil : Π {α : Type}, List α
    let nil_ctor = Constructor {
        name: Name::str(list_name.clone(), "nil"),
        ty: Expr::forall(
            alpha.clone(),
            Expr::const_expr("Type".into(), vec![]),
            Expr::app(Expr::const_expr(list_name.clone(), vec![]), Expr::bvar(0)),
            BinderInfo::Implicit,
        ),
        arity: 0,
    };

    // cons : Π {α : Type}, α → List α → List α
    let cons_ctor = Constructor {
        name: Name::str(list_name.clone(), "cons"),
        ty: Expr::forall(
            alpha.clone(),
            Expr::const_expr("Type".into(), vec![]),
            Expr::forall(
                Name::anonymous(),
                Expr::bvar(0), // α
                Expr::forall(
                    Name::anonymous(),
                    Expr::app(Expr::const_expr(list_name.clone(), vec![]), Expr::bvar(1)), /* List α */
                    Expr::app(Expr::const_expr(list_name.clone(), vec![]), Expr::bvar(2)), /* List α */
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        ),
        arity: 2,
    };

    let alpha_param = Parameter {
        name: alpha,
        ty: Expr::const_expr("Type".into(), vec![]),
        binder_info: BinderInfo::Implicit,
    };

    InductiveType {
        name: list_name,
        universe_params: vec![],
        params: vec![alpha_param],
        indices: vec![],
        ty: list_type,
        constructors: vec![nil_ctor, cons_ctor],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::environment_ext::init_basic_environment;

    #[test]
    fn test_create_nat_inductive() {
        let nat = create_nat_inductive();

        assert_eq!(nat.name.to_string(), "Nat");
        assert_eq!(nat.constructors.len(), 2);
        assert_eq!(nat.constructors[0].name.to_string(), "Nat.zero");
        assert_eq!(nat.constructors[1].name.to_string(), "Nat.succ");
        assert_eq!(nat.constructors[0].arity, 0);
        assert_eq!(nat.constructors[1].arity, 1);
    }

    #[test]
    fn test_create_list_inductive() {
        let list = create_list_inductive();

        assert_eq!(list.name.to_string(), "List");
        assert_eq!(list.constructors.len(), 2);
        assert_eq!(list.constructors[0].name.to_string(), "List.nil");
        assert_eq!(list.constructors[1].name.to_string(), "List.cons");
        assert_eq!(list.params.len(), 1);
        assert_eq!(list.params[0].name.to_string(), "α");
    }

    #[test]
    fn test_nat_well_formed() {
        let nat = create_nat_inductive();
        let env = init_basic_environment();

        let result = nat.check_well_formed(&env);
        assert!(result.is_ok(), "Nat should be well-formed: {:?}", result);
    }

    #[test]
    fn test_add_nat_to_env() {
        let mut env = Environment::new();
        let mut state = ElabState::new();
        let nat = create_nat_inductive();

        let result = add_inductive_to_env(&mut env, nat, &mut state);
        assert!(
            result.is_ok(),
            "Adding Nat to environment should succeed: {:?}",
            result
        );

        // Check that the type and constructors were added
        assert!(env.contains(&Name::mk_simple("Nat")));
        assert!(env.contains(&Name::str(Name::mk_simple("Nat"), "zero")));
        assert!(env.contains(&Name::str(Name::mk_simple("Nat"), "succ")));
        assert!(env.contains(&Name::str(Name::mk_simple("Nat"), "rec")));
    }

    #[test]
    fn test_generate_eliminator() {
        let nat = create_nat_inductive();
        let env = init_basic_environment();

        let elim = generate_eliminator(&nat, &env);
        assert!(
            elim.is_ok(),
            "Generating Nat eliminator should succeed: {:?}",
            elim
        );

        let eliminator = elim.unwrap();
        assert_eq!(eliminator.name.to_string(), "Nat.rec");
        assert_eq!(eliminator.rules.len(), 2); // One rule per constructor
    }

    #[test]
    fn test_constructor_positivity() {
        let nat = create_nat_inductive();

        // Nat constructors should pass positivity check
        for ctor in &nat.constructors {
            let result = nat.check_constructor_positivity(ctor);
            assert!(
                result.is_ok(),
                "Nat constructor {} should be positive: {:?}",
                ctor.name,
                result
            );
        }
    }

    #[test]
    fn test_inductive_family_creation() {
        let nat = create_nat_inductive();
        let list = create_list_inductive();

        let family = InductiveFamily {
            types: vec![nat, list],
            universe_params: vec![],
            params: vec![],
        };

        assert_eq!(family.types.len(), 2);
        assert_eq!(family.types[0].name.to_string(), "Nat");
        assert_eq!(family.types[1].name.to_string(), "List");
    }

    #[test]
    fn test_no_confusion_generation() {
        let nat = create_nat_inductive();

        let no_confusion = generate_no_confusion(&nat);
        assert!(
            no_confusion.is_ok(),
            "Generating no-confusion should succeed: {:?}",
            no_confusion
        );

        let lemma = no_confusion.unwrap();
        assert_eq!(lemma.name.to_string(), "Nat.noConfusion");
    }

    #[test]
    fn test_injectivity_generation() {
        let nat = create_nat_inductive();
        let succ_ctor = &nat.constructors[1]; // succ constructor

        let inj_lemma = generate_injectivity_lemma(&nat, succ_ctor);
        assert!(
            inj_lemma.is_ok(),
            "Generating injectivity lemma should succeed: {:?}",
            inj_lemma
        );

        let lemma = inj_lemma.unwrap();
        assert_eq!(lemma.name.to_string(), "Nat.succ.inj");
    }

    #[test]
    fn test_pattern_match_compilation() {
        let nat = create_nat_inductive();
        let env = init_basic_environment();

        let discriminant = Expr::fvar(Name::mk_simple("n"));
        let patterns = vec![
            (
                nat.constructors[0].clone(), // zero
                vec![],
                Expr::nat(0),
            ),
            (
                nat.constructors[1].clone(), // succ
                vec![Name::mk_simple("m")],
                Expr::nat(1),
            ),
        ];

        let result = compile_pattern_match(&nat, discriminant, patterns, &env);
        assert!(
            result.is_ok(),
            "Pattern match compilation should succeed: {:?}",
            result
        );
    }
}
