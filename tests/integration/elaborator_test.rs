use lean_elaborator::Elaborator;
use lean_kernel::expr::ExprKind;
use lean_parser::Parser;

#[test]
fn test_elaborate_lambda_identity() {
    let mut parser = Parser::new("λ x => x");
    let syntax = parser.term().unwrap();

    let mut elab = Elaborator::new();
    let expr = elab.elaborate(&syntax).unwrap();

    // Check it's a lambda
    match &expr.kind {
        ExprKind::Lam(name, _ty, body, _) => {
            assert_eq!(name.to_string(), "x");
            // Body should be bvar(0)
            assert!(matches!(&body.kind, ExprKind::BVar(0)));
        }
        _ => panic!("Expected lambda"),
    }
}

#[test]
fn test_elaborate_nested_lambda() {
    let mut parser = Parser::new("λ x => λ y => x");
    let syntax = parser.term().unwrap();

    let mut elab = Elaborator::new();
    let expr = elab.elaborate(&syntax).unwrap();

    // Check outer lambda
    match &expr.kind {
        ExprKind::Lam(_x_name, _, body, _) => {
            // Body should be another lambda
            match &body.kind {
                ExprKind::Lam(_y_name, _, inner_body, _) => {
                    // Inner body should be bvar(1) (referring to x)
                    assert!(matches!(&inner_body.kind, ExprKind::BVar(1)));
                }
                _ => panic!("Expected inner lambda"),
            }
        }
        _ => panic!("Expected outer lambda"),
    }
}

#[test]
fn test_elaborate_application() {
    let mut parser = Parser::new("f x y");
    let syntax = parser.term().unwrap();

    let mut elab = Elaborator::new();

    // Add the identifiers to the local context so they can be resolved
    use lean_kernel::{expr::BinderInfo, Expr, Name};
    let nat_type = Expr::const_expr("Nat".into(), vec![]);

    // f : Nat → Nat → Nat (a function that takes two Nats and returns a Nat)
    let f_type = Expr::forall(
        Name::mk_simple("_"),
        nat_type.clone(),
        Expr::forall(
            Name::mk_simple("_"),
            nat_type.clone(),
            nat_type.clone(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let f_id = elab
        .state_mut()
        .lctx
        .push_local_decl(Name::mk_simple("f"), f_type);
    let x_id = elab
        .state_mut()
        .lctx
        .push_local_decl(Name::mk_simple("x"), nat_type.clone());
    let y_id = elab
        .state_mut()
        .lctx
        .push_local_decl(Name::mk_simple("y"), nat_type);

    let expr = elab.elaborate(&syntax).unwrap();

    // Should be App(App(f, x), y) with FVars
    match &expr.kind {
        ExprKind::App(f_x, y) => {
            match &f_x.kind {
                ExprKind::App(f, x) => {
                    // Check we have the right free variables
                    assert!(matches!(&f.kind, ExprKind::FVar(name) if name == &f_id));
                    assert!(matches!(&x.kind, ExprKind::FVar(name) if name == &x_id));
                }
                _ => panic!("Expected nested application"),
            }
            assert!(matches!(&y.kind, ExprKind::FVar(name) if name == &y_id));
        }
        _ => panic!("Expected application"),
    }
}

#[test]
fn test_elaborate_let_binding() {
    let mut parser = Parser::new("let x := 5 in x");
    let syntax = parser.term().unwrap();

    let mut elab = Elaborator::new();
    let expr = elab.elaborate(&syntax).unwrap();

    // Check let expression
    match &expr.kind {
        ExprKind::Let(name, _ty, value, body) => {
            assert_eq!(name.to_string(), "x");
            // Value should be literal 5
            assert!(matches!(
                &value.kind,
                ExprKind::Lit(lean_kernel::expr::Literal::Nat(5))
            ));
            // Body should be bvar(0)
            assert!(matches!(&body.kind, ExprKind::BVar(0)));
        }
        _ => panic!("Expected let expression"),
    }
}

#[test]
fn test_elaborate_arrow_type() {
    let mut parser = Parser::new("Nat → Bool");
    let syntax = parser.term().unwrap();

    let mut elab = Elaborator::new();
    let expr = elab.elaborate(&syntax).unwrap();

    // Arrow should be sugar for forall
    match &expr.kind {
        ExprKind::Forall(name, domain, codomain, _) => {
            assert!(name.is_anonymous());
            assert!(matches!(&domain.kind, ExprKind::Const(n, _) if n.to_string() == "Nat"));
            assert!(matches!(&codomain.kind, ExprKind::Const(n, _) if n.to_string() == "Bool"));
        }
        _ => panic!("Expected forall (arrow type)"),
    }
}

#[test]
fn test_elaborate_with_metavars() {
    // Lambda without type annotation creates metavariable for binder type
    let mut parser = Parser::new("λ x => x");
    let syntax = parser.term().unwrap();

    let mut elab = Elaborator::new();
    let expr = elab.elaborate(&syntax).unwrap();

    match &expr.kind {
        ExprKind::Lam(_name, ty, _body, _) => {
            // Type should be a metavariable
            assert!(matches!(&ty.kind, ExprKind::MVar(_)));
        }
        _ => panic!("Expected lambda"),
    }
}

#[test]
fn test_implicit_args_synthesis_integration() {
    use lean_kernel::{expr::BinderInfo, Expr, Level, Name};

    // Test implicit argument synthesis more directly by just parsing "id"
    // and checking that synthesis works
    let mut elab = Elaborator::new();

    // Create an identity function type: {α : Type} → α → α
    let type_sort = Expr::sort(Level::zero());
    let alpha_var = Expr::bvar(0);
    let arrow_type = Expr::forall(
        Name::mk_simple("_"),
        alpha_var.clone(),
        alpha_var.clone(),
        BinderInfo::Default,
    );
    let id_type = Expr::forall(
        Name::mk_simple("α"),
        type_sort,
        arrow_type,
        BinderInfo::Implicit,
    );

    // Add the identity function to the local context
    let id_name = Name::mk_simple("id");
    let id_fvar_id = elab
        .state_mut()
        .lctx
        .push_local_decl(id_name.clone(), id_type);

    // Parse just "id" and verify synthesis works directly
    let mut parser = Parser::new("id");
    let syntax = parser.term().expect("Failed to parse");

    // Elaborate the syntax - but don't expect synthesis since we're not applying
    let result = elab.elaborate(&syntax).expect("Failed to elaborate");

    // The result should just be the function itself, no implicit args synthesized
    // yet
    match &result.kind {
        ExprKind::FVar(name) => {
            assert_eq!(name, &id_fvar_id);
        }
        _ => panic!("Expected simple FVar for id function"),
    }

    // Now test that synthesis_implicit_args works on this function
    let synthesized = elab
        .synthesize_implicit_args(result)
        .expect("Failed to synthesize");

    // Now we should have an application: App(id, ?mvar)
    match &synthesized.kind {
        ExprKind::App(id_f, impl_arg) => {
            // id_f should be the identity function
            match &id_f.kind {
                ExprKind::FVar(name) => {
                    assert_eq!(name, &id_fvar_id);
                }
                _ => panic!("Expected FVar for id function"),
            }

            // impl_arg should be a metavariable
            match &impl_arg.kind {
                ExprKind::MVar(_) => {
                    // This is what we expect - implicit argument was
                    // synthesized
                }
                _ => panic!("Expected metavariable for implicit argument"),
            }
        }
        _ => panic!("Expected application with synthesized implicit arg"),
    }
}

#[test]
fn test_instance_resolution_with_elaboration() {
    use lean_elaborator::Instance;
    use lean_kernel::{Expr, Name};

    // Test that instance resolution integrates properly with elaboration
    let mut elab = Elaborator::new();

    // Set up an Add Nat instance
    let add_nat_ty = Expr::app(
        Expr::const_expr("Add".into(), vec![]),
        Expr::const_expr("Nat".into(), vec![]),
    );
    let add_nat_instance = Instance {
        name: Name::mk_simple("AddNat"),
        ty: add_nat_ty.clone(),
        priority: 100,
    };

    // Add to instance context
    elab.state_mut().inst_ctx.add_instance(add_nat_instance);

    // Verify the instance was added
    let instances = elab.state().inst_ctx.find_instances(&add_nat_ty);
    assert_eq!(instances.len(), 1);
    assert_eq!(instances[0].name.to_string(), "AddNat");
    assert_eq!(instances[0].priority, 100);

    // Test that the instance context is properly integrated
    assert!(elab
        .state()
        .inst_ctx
        .find_instances(&Expr::const_expr("Nonexistent".into(), vec![]))
        .is_empty());
}
