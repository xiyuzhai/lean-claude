use expect_test::{expect, Expect};

use super::*;

fn check_expr_debug(expr: &Expr, expected: Expect) {
    let output = format!("{expr:#?}");
    expected.assert_eq(&output);
}

#[test]
fn test_bvar_creation() {
    let expr = Expr::bvar(0);
    assert!(expr.is_bvar());
    assert!(!expr.is_fvar());

    check_expr_debug(
        &expr,
        expect![[r#"
            Expr {
                kind: BVar(
                    0,
                ),
            }"#]],
    );
}

#[test]
fn test_fvar_creation() {
    let name = Name::from("x");
    let expr = Expr::fvar(name.clone());
    assert!(expr.is_fvar());
    assert!(!expr.is_bvar());

    if let ExprKind::FVar(n) = &expr.kind {
        assert_eq!(n, &name);
    } else {
        panic!("Expected FVar");
    }
}

#[test]
fn test_app_creation() {
    let f = Expr::fvar(Name::from("f"));
    let arg = Expr::fvar(Name::from("x"));
    let app = Expr::app(f, arg);

    assert!(app.is_app());

    check_expr_debug(
        &app,
        expect![[r#"
            Expr {
                kind: App(
                    Expr {
                        kind: FVar(
                            Str(
                                Anonymous,
                                BaseCoword {
                                    data: "f",
                                },
                            ),
                        ),
                    },
                    Expr {
                        kind: FVar(
                            Str(
                                Anonymous,
                                BaseCoword {
                                    data: "x",
                                },
                            ),
                        ),
                    },
                ),
            }"#]],
    );
}

#[test]
fn test_lambda_creation() {
    let name = Name::from("x");
    let ty = Expr::sort(Level::zero());
    let body = Expr::bvar(0);
    let lam = Expr::lam(name, ty, body, BinderInfo::Default);

    assert!(lam.is_lambda());
    assert!(!lam.is_forall());
}

#[test]
fn test_forall_creation() {
    let name = Name::from("x");
    let ty = Expr::sort(Level::zero());
    let body = Expr::sort(Level::zero());
    let forall = Expr::forall(name, ty, body, BinderInfo::Implicit);

    assert!(forall.is_forall());
    assert!(!forall.is_lambda());
}

#[test]
fn test_let_expr_creation() {
    let name = Name::from("x");
    let ty = Expr::sort(Level::zero());
    let value = Expr::nat(42);
    let body = Expr::bvar(0);
    let let_expr = Expr::let_expr(name, ty, value, body);

    assert!(let_expr.is_let());
}

#[test]
fn test_literal_creation() {
    let nat_expr = Expr::nat(42);
    let string_expr = Expr::string("hello");

    match &nat_expr.kind {
        ExprKind::Lit(Literal::Nat(n)) => assert_eq!(*n, 42),
        _ => panic!("Expected Nat literal"),
    }

    match &string_expr.kind {
        ExprKind::Lit(Literal::String(s)) => assert_eq!(s.as_str(), "hello"),
        _ => panic!("Expected String literal"),
    }
}

#[test]
fn test_proj_creation() {
    let struct_name = Name::from("Point");
    let expr = Expr::fvar(Name::from("p"));
    let proj = Expr::proj(struct_name, 0, expr);

    match &proj.kind {
        ExprKind::Proj(name, idx, _) => {
            assert_eq!(name.to_string(), "Point");
            assert_eq!(*idx, 0);
        }
        _ => panic!("Expected Proj"),
    }
}

#[test]
fn test_loose_bvar_range() {
    // No loose bvars
    let expr1 = Expr::fvar(Name::from("x"));
    assert_eq!(expr1.loose_bvar_range(), 0);
    assert!(!expr1.has_loose_bvars());

    // BVar(0) is loose
    let expr2 = Expr::bvar(0);
    assert_eq!(expr2.loose_bvar_range(), 1);
    assert!(expr2.has_loose_bvars());

    // BVar(2) gives range 3
    let expr3 = Expr::bvar(2);
    assert_eq!(expr3.loose_bvar_range(), 3);

    // Lambda binds one variable
    let lam = Expr::lam(
        Name::from("x"),
        Expr::sort(Level::zero()),
        Expr::bvar(0), // This is bound by the lambda
        BinderInfo::Default,
    );
    assert_eq!(lam.loose_bvar_range(), 0);
    assert!(!lam.has_loose_bvars());

    // Lambda with loose bvar
    let lam_loose = Expr::lam(
        Name::from("x"),
        Expr::sort(Level::zero()),
        Expr::bvar(1), // This refers to an outer binding
        BinderInfo::Default,
    );
    assert_eq!(lam_loose.loose_bvar_range(), 1);
    assert!(lam_loose.has_loose_bvars());
}

#[test]
fn test_app_loose_bvars() {
    let f = Expr::bvar(0);
    let arg = Expr::bvar(1);
    let app = Expr::app(f, arg);

    // Should be max(1, 2) = 2
    assert_eq!(app.loose_bvar_range(), 2);
}

#[test]
fn test_let_loose_bvars() {
    let let_expr = Expr::let_expr(
        Name::from("x"),
        Expr::bvar(0), // Type has loose bvar
        Expr::bvar(1), // Value has loose bvar
        Expr::bvar(0), // Body refers to let-bound var (not loose)
    );

    // Should be max(1, 2, 0) = 2
    assert_eq!(let_expr.loose_bvar_range(), 2);
}

#[test]
fn test_binder_info_display() {
    assert_eq!(BinderInfo::Default.to_string(), "");
    assert_eq!(BinderInfo::Implicit.to_string(), "{}");
    assert_eq!(BinderInfo::StrictImplicit.to_string(), "⦃⦄");
    assert_eq!(BinderInfo::InstImplicit.to_string(), "[]");
}

#[test]
fn test_complex_expr() {
    // Build: λ (f : α → β) (x : α), f x
    let alpha = Expr::fvar(Name::from("α"));
    let beta = Expr::fvar(Name::from("β"));
    let arrow_type = Expr::forall(
        Name::from("_"),
        alpha.clone(),
        beta.clone(),
        BinderInfo::Default,
    );

    let f_var = Expr::bvar(1); // f
    let x_var = Expr::bvar(0); // x
    let app = Expr::app(f_var, x_var);

    let inner_lam = Expr::lam(Name::from("x"), alpha.clone(), app, BinderInfo::Default);

    let outer_lam = Expr::lam(Name::from("f"), arrow_type, inner_lam, BinderInfo::Default);

    assert!(outer_lam.is_lambda());
    assert_eq!(outer_lam.loose_bvar_range(), 0);
}

#[test]
fn test_mdata() {
    let name = Name::from("meta");
    let expr = Expr::nat(42);
    let data = vec![Expr::string("info")];

    let mdata = MData {
        name: name.clone(),
        data,
    };
    let wrapped = Expr {
        kind: ExprKind::MData(mdata, Box::new(expr)),
    };

    match &wrapped.kind {
        ExprKind::MData(md, inner) => {
            assert_eq!(md.name, name);
            assert_eq!(md.data.len(), 1);
            matches!(inner.kind, ExprKind::Lit(Literal::Nat(42)));
        }
        _ => panic!("Expected MData"),
    }
}
