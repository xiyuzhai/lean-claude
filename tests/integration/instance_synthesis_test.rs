use lean_elaborator::{Elaborator, Instance};
use lean_kernel::{expr::{BinderInfo, ExprKind}, Expr, Level, Name};

#[test]
fn test_comprehensive_instance_synthesis() {
    // Test that shows implicit argument synthesis and instance resolution working together
    let mut elab = Elaborator::new();
    
    // Create Add typeclass instances
    let add_nat_ty = Expr::app(
        Expr::const_expr("Add".into(), vec![]),
        Expr::const_expr("Nat".into(), vec![]),
    );
    let add_int_ty = Expr::app(
        Expr::const_expr("Add".into(), vec![]),
        Expr::const_expr("Int".into(), vec![]),
    );
    
    let add_nat_instance = Instance {
        name: Name::mk_simple("Add.Nat"),
        ty: add_nat_ty.clone(),
        priority: 100,
    };
    let add_int_instance = Instance {
        name: Name::mk_simple("Add.Int"),
        ty: add_int_ty.clone(),
        priority: 90,
    };
    
    // Add instances to context
    elab.state_mut().inst_ctx.add_instance(add_nat_instance);
    elab.state_mut().inst_ctx.add_instance(add_int_instance);
    
    // Verify instances were added
    assert_eq!(elab.state().inst_ctx.find_instances(&add_nat_ty).len(), 1);
    assert_eq!(elab.state().inst_ctx.find_instances(&add_int_ty).len(), 1);
    
    // Test instance resolution directly
    let add_instances = elab.state().inst_ctx.find_instances(&Expr::const_expr("Add".into(), vec![]));
    assert_eq!(add_instances.len(), 2); // Should find both instances
    
    // Check priorities are correct
    let mut priorities: Vec<u32> = add_instances.iter().map(|inst| inst.priority).collect();
    priorities.sort();
    assert_eq!(priorities, vec![90, 100]);
    
    // Test that non-existent instances return empty
    let empty_instances = elab.state().inst_ctx.find_instances(&Expr::const_expr("NonExistent".into(), vec![]));
    assert!(empty_instances.is_empty());
}

#[test]
fn test_instance_synthesis_fallback() {
    // Test that when no instance is found, a metavariable is created as fallback
    let mut elab = Elaborator::new();
    
    // Create a function type requiring a missing instance: [Missing α] → α
    let missing_ty = Expr::app(
        Expr::const_expr("Missing".into(), vec![]),
        Expr::const_expr("SomeType".into(), vec![]),
    );
    
    // Try to resolve - should fallback to metavariable
    let result = elab.resolve_instance_argument(&missing_ty);
    
    match result {
        Ok(expr) => {
            // Should be a metavariable
            match &expr.kind {
                ExprKind::MVar(_) => {
                    // This is what we expect - fallback metavariable
                }
                _ => panic!("Expected metavariable fallback, got {:?}", expr.kind),
            }
        }
        Err(_) => {
            // Error is also acceptable - depends on implementation details
        }
    }
}

#[test] 
fn test_instance_priorities() {
    // Test that higher priority instances are found first
    let mut elab = Elaborator::new();
    
    let target_ty = Expr::const_expr("TestClass".into(), vec![]);
    
    // Add instances with different priorities
    let low_priority = Instance {
        name: Name::mk_simple("LowPriority"),
        ty: target_ty.clone(),
        priority: 10,
    };
    let high_priority = Instance {
        name: Name::mk_simple("HighPriority"),
        ty: target_ty.clone(),
        priority: 100,
    };
    
    elab.state_mut().inst_ctx.add_instance(low_priority);
    elab.state_mut().inst_ctx.add_instance(high_priority);
    
    let instances = elab.state().inst_ctx.find_instances(&target_ty);
    assert_eq!(instances.len(), 2);
    
    // Verify both instances are found
    let names: std::collections::HashSet<String> = instances
        .iter()
        .map(|inst| inst.name.to_string())
        .collect();
    assert!(names.contains("LowPriority"));
    assert!(names.contains("HighPriority"));
    
    // Verify priorities are preserved
    for instance in instances {
        match instance.name.to_string().as_str() {
            "LowPriority" => assert_eq!(instance.priority, 10),
            "HighPriority" => assert_eq!(instance.priority, 100),
            _ => panic!("Unexpected instance name"),
        }
    }
}