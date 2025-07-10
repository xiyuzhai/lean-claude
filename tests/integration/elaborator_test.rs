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
    let expr = elab.elaborate(&syntax).unwrap();

    // Should be App(App(f, x), y)
    match &expr.kind {
        ExprKind::App(f_x, y) => {
            match &f_x.kind {
                ExprKind::App(f, x) => {
                    // Check we have the right constants
                    assert!(matches!(&f.kind, ExprKind::Const(name, _) if name.to_string() == "f"));
                    assert!(matches!(&x.kind, ExprKind::Const(name, _) if name.to_string() == "x"));
                }
                _ => panic!("Expected nested application"),
            }
            assert!(matches!(&y.kind, ExprKind::Const(name, _) if name.to_string() == "y"));
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
