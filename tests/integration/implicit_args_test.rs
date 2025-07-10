use lean_elaborator::elab::{ElabState, Elaborator};
use lean_kernel::{expr::BinderInfo, Expr, Level, Name};
use lean_parser::Parser;
use lean_syn_expr::Syntax;

#[test]
fn test_implicit_args_with_parser_integration() {
    // Test that implicit argument synthesis works with parsed syntax
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
    let id_fvar_id = elab.state_mut().lctx.push_local_decl(id_name.clone(), id_type);
    
    // Parse an application: "id x"
    let mut parser = Parser::new("id x");
    let syntax = parser.term().expect("Failed to parse");
    
    // Add x to the context with some type
    let x_name = Name::mk_simple("x");
    let x_type = Expr::const_expr("Nat".into(), vec![]); // Assume x : Nat
    let _x_fvar_id = elab.state_mut().lctx.push_local_decl(x_name, x_type);
    
    // Elaborate the syntax - this should synthesize the implicit type argument
    let result = elab.elaborate(&syntax).expect("Failed to elaborate");
    
    // The result should be an application: App(App(id, ?mvar), x)
    // where ?mvar is a metavariable for the implicit type argument
    match &result.kind {
        lean_kernel::expr::ExprKind::App(f_with_impl, x_arg) => {
            // x_arg should be the explicit argument (x)
            match &x_arg.kind {
                lean_kernel::expr::ExprKind::FVar(_) => (), // Expected
                _ => panic!("Expected FVar for x argument"),
            }
            
            // f_with_impl should be (id ?mvar)
            match &f_with_impl.kind {
                lean_kernel::expr::ExprKind::App(id_f, impl_arg) => {
                    // id_f should be the identity function
                    match &id_f.kind {
                        lean_kernel::expr::ExprKind::FVar(name) => {
                            assert_eq!(name, &id_fvar_id);
                        }
                        _ => panic!("Expected FVar for id function"),
                    }
                    
                    // impl_arg should be a metavariable
                    match &impl_arg.kind {
                        lean_kernel::expr::ExprKind::MVar(_) => {
                            // This is what we expect - implicit argument was synthesized
                        }
                        _ => panic!("Expected metavariable for implicit argument"),
                    }
                }
                _ => panic!("Expected nested application for id with implicit arg"),
            }
        }
        _ => panic!("Expected application at top level"),
    }
}

#[test]
fn test_no_implicit_synthesis_for_explicit() {
    // Test that explicit arguments don't trigger synthesis
    let mut elab = Elaborator::new();
    
    // Create a simple function type: α → α (no implicit args)
    let alpha_var = Expr::bvar(0);
    let simple_type = Expr::forall(
        Name::mk_simple("α"),
        Expr::sort(Level::zero()),
        Expr::forall(
            Name::mk_simple("_"),
            alpha_var.clone(), 
            alpha_var.clone(),
            BinderInfo::Default,
        ),
        BinderInfo::Default, // Explicit argument
    );
    
    // Add the function to the local context
    let f_name = Name::mk_simple("f");
    let f_fvar_id = elab.state_mut().lctx.push_local_decl(f_name.clone(), simple_type);
    
    // Parse an application: "f x"
    let mut parser = Parser::new("f x");
    let syntax = parser.term().expect("Failed to parse");
    
    // Add x to the context
    let x_name = Name::mk_simple("x");
    let x_type = Expr::const_expr("Type".into(), vec![]);
    let _x_fvar_id = elab.state_mut().lctx.push_local_decl(x_name, x_type);
    
    // Elaborate the syntax - should not synthesize any implicit arguments
    let result = elab.elaborate(&syntax).expect("Failed to elaborate");
    
    // The result should be a simple application: App(f, x)
    match &result.kind {
        lean_kernel::expr::ExprKind::App(f_expr, x_expr) => {
            // f_expr should be just the function, not applied to any implicit args
            match &f_expr.kind {
                lean_kernel::expr::ExprKind::FVar(name) => {
                    assert_eq!(name, &f_fvar_id);
                }
                _ => panic!("Expected simple FVar for function, not applied to implicits"),
            }
            
            // x_expr should be the explicit argument
            match &x_expr.kind {
                lean_kernel::expr::ExprKind::FVar(_) => (), // Expected
                _ => panic!("Expected FVar for x argument"),
            }
        }
        _ => panic!("Expected simple application"),
    }
}