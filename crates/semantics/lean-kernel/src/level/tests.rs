use expect_test::{expect, Expect};

use super::*;

fn check_level_display(level: &Level, expected: &str) {
    assert_eq!(level.to_string(), expected);
}

fn check_level_debug(level: &Level, expected: Expect) {
    let output = format!("{level:#?}");
    expected.assert_eq(&output);
}

#[test]
fn test_zero_level() {
    let level = Level::zero();
    assert!(level.is_zero());
    assert!(!level.is_succ());
    check_level_display(&level, "0");

    check_level_debug(
        &level,
        expect![[r#"
            Level {
                kind: Zero,
            }"#]],
    );
}

#[test]
fn test_succ_level() {
    let level = Level::succ(Level::zero());
    assert!(level.is_succ());
    assert!(!level.is_zero());
    check_level_display(&level, "0 + 1");

    // Test multiple successors
    let level2 = Level::succ(Level::succ(Level::zero()));
    check_level_display(&level2, "0 + 1 + 1");
}

#[test]
fn test_max_level() {
    let l1 = Level::param(Name::from("u"));
    let l2 = Level::param(Name::from("v"));
    let max = Level::max(l1, l2);

    assert!(max.is_max());
    check_level_display(&max, "max u v");
}

#[test]
fn test_imax_level() {
    let l1 = Level::param(Name::from("u"));
    let l2 = Level::param(Name::from("v"));
    let imax = Level::imax(l1, l2);

    assert!(imax.is_imax());
    check_level_display(&imax, "imax u v");
}

#[test]
fn test_param_level() {
    let level = Level::param(Name::from("u"));
    assert!(level.is_param());
    check_level_display(&level, "u");

    // Test hierarchical parameter name
    let level2 = Level::param(Name::from("Type.u"));
    check_level_display(&level2, "Type.u");
}

#[test]
fn test_mvar_level() {
    let level = Level::mvar(Name::from("m"));
    assert!(level.is_mvar());
    check_level_display(&level, "?m");
}

#[test]
fn test_normalize_max() {
    // max 0 u = u
    let l1 = Level::max(Level::zero(), Level::param(Name::from("u")));
    let normalized = l1.normalize();
    assert_eq!(normalized, Level::param(Name::from("u")));

    // max u 0 = u
    let l2 = Level::max(Level::param(Name::from("u")), Level::zero());
    let normalized = l2.normalize();
    assert_eq!(normalized, Level::param(Name::from("u")));

    // max u u = u
    let u = Level::param(Name::from("u"));
    let l3 = Level::max(u.clone(), u.clone());
    let normalized = l3.normalize();
    assert_eq!(normalized, u);

    // max u v = max u v (no normalization)
    let v = Level::param(Name::from("v"));
    let l4 = Level::max(u.clone(), v.clone());
    let normalized = l4.normalize();
    assert_eq!(normalized, Level::max(u, v));
}

#[test]
fn test_normalize_imax() {
    // imax u 0 = 0
    let l1 = Level::imax(Level::param(Name::from("u")), Level::zero());
    let normalized = l1.normalize();
    assert_eq!(normalized, Level::zero());

    // imax 0 u = u
    let l2 = Level::imax(Level::zero(), Level::param(Name::from("u")));
    let normalized = l2.normalize();
    assert_eq!(normalized, Level::param(Name::from("u")));

    // imax u v = imax u v (no normalization when both non-zero)
    let u = Level::param(Name::from("u"));
    let v = Level::param(Name::from("v"));
    let l3 = Level::imax(u.clone(), v.clone());
    let normalized = l3.normalize();
    assert_eq!(normalized, Level::imax(u, v));
}

#[test]
fn test_complex_level() {
    // Build: max (u + 1) (imax v w)
    let u = Level::param(Name::from("u"));
    let v = Level::param(Name::from("v"));
    let w = Level::param(Name::from("w"));

    let u_succ = Level::succ(u);
    let imax_vw = Level::imax(v, w);
    let complex = Level::max(u_succ, imax_vw);

    check_level_display(&complex, "max u + 1 imax v w");
}

#[test]
fn test_normalize_nested() {
    // max (max 0 u) (max v 0) should normalize to max u v
    let u = Level::param(Name::from("u"));
    let v = Level::param(Name::from("v"));

    let inner1 = Level::max(Level::zero(), u.clone());
    let inner2 = Level::max(v.clone(), Level::zero());
    let outer = Level::max(inner1, inner2);

    let normalized = outer.normalize();
    assert_eq!(normalized, Level::max(u, v));
}

#[test]
fn test_level_equality() {
    let l1 = Level::succ(Level::param(Name::from("u")));
    let l2 = Level::succ(Level::param(Name::from("u")));
    assert_eq!(l1, l2);

    let l3 = Level::succ(Level::param(Name::from("v")));
    assert_ne!(l1, l3);
}

#[test]
fn test_level_hash() {
    use std::collections::HashSet;

    let mut set = HashSet::new();
    set.insert(Level::zero());
    set.insert(Level::param(Name::from("u")));
    set.insert(Level::zero()); // Duplicate

    assert_eq!(set.len(), 2);
    assert!(set.contains(&Level::zero()));
    assert!(set.contains(&Level::param(Name::from("u"))));
}
