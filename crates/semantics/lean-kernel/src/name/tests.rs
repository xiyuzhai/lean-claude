use expect_test::{expect, Expect};

use super::*;

fn check_name_display(name: &Name, expected: &str) {
    assert_eq!(name.to_string(), expected);
}

fn check_name_debug(name: &Name, expected: Expect) {
    let output = format!("{name:#?}");
    expected.assert_eq(&output);
}

#[test]
fn test_anonymous_name() {
    let name = Name::anonymous();
    assert!(name.is_anonymous());
    assert!(name.is_atomic());
    check_name_display(&name, "[anonymous]");
}

#[test]
fn test_simple_name() {
    let name = Name::mk_simple("foo");
    assert!(!name.is_anonymous());
    assert!(name.is_atomic());
    check_name_display(&name, "foo");

    check_name_debug(
        &name,
        expect![[r#"
            Str(
                Anonymous,
                BaseCoword {
                    data: "foo",
                },
            )"#]],
    );
}

#[test]
fn test_hierarchical_name() {
    let name = Name::str(Name::mk_simple("Foo"), "bar");
    assert!(!name.is_anonymous());
    assert!(!name.is_atomic());
    check_name_display(&name, "Foo.bar");

    let components = name.components();
    assert_eq!(components, vec!["Foo", "bar"]);
}

#[test]
fn test_numeric_name() {
    let name = Name::num(Name::mk_simple("foo"), 42);
    assert!(!name.is_anonymous());
    assert!(!name.is_atomic());
    check_name_display(&name, "foo.42");

    let components = name.components();
    assert_eq!(components, vec!["foo", "42"]);
}

#[test]
fn test_from_str_simple() {
    let name = Name::from("foo");
    check_name_display(&name, "foo");
    assert!(name.is_atomic());
}

#[test]
fn test_from_str_hierarchical() {
    let name = Name::from("Foo.Bar.baz");
    check_name_display(&name, "Foo.Bar.baz");
    assert!(!name.is_atomic());

    let components = name.components();
    assert_eq!(components, vec!["Foo", "Bar", "baz"]);
}

#[test]
fn test_from_str_with_numbers() {
    let name = Name::from("foo.42.bar.7");
    check_name_display(&name, "foo.42.bar.7");

    let components = name.components();
    assert_eq!(components, vec!["foo", "42", "bar", "7"]);
}

#[test]
fn test_from_str_empty() {
    let name = Name::from("");
    assert!(name.is_anonymous());
    check_name_display(&name, "[anonymous]");
}

#[test]
fn test_complex_name_construction() {
    // Build Mathlib.Data.Nat.Basic step by step
    let mathlib = Name::mk_simple("Mathlib");
    let data = Name::str(mathlib, "Data");
    let nat = Name::str(data, "Nat");
    let basic = Name::str(nat, "Basic");

    check_name_display(&basic, "Mathlib.Data.Nat.Basic");

    let components = basic.components();
    assert_eq!(components, vec!["Mathlib", "Data", "Nat", "Basic"]);
}

#[test]
fn test_name_equality() {
    let name1 = Name::from("Foo.bar");
    let name2 = Name::str(Name::mk_simple("Foo"), "bar");
    assert_eq!(name1, name2);

    let name3 = Name::from("Foo.baz");
    assert_ne!(name1, name3);
}

#[test]
fn test_name_hash() {
    use std::collections::HashSet;

    let mut set = HashSet::new();
    set.insert(Name::from("foo"));
    set.insert(Name::from("bar"));
    set.insert(Name::from("foo")); // Duplicate

    assert_eq!(set.len(), 2);
    assert!(set.contains(&Name::from("foo")));
    assert!(set.contains(&Name::from("bar")));
}

#[test]
fn test_mixed_numeric_string_components() {
    let name = Name::num(
        Name::str(Name::num(Name::mk_simple("level"), 3), "meta"),
        99,
    );

    check_name_display(&name, "level.3.meta.99");

    let components = name.components();
    assert_eq!(components, vec!["level", "3", "meta", "99"]);
}
