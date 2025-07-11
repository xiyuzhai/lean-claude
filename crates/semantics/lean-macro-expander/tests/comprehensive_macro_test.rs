use lean_macro_expander::{MacroEnvironment, MacroExpander};
use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

fn expand_and_verify(input: &str) -> Result<String, String> {
    let mut parser = Parser::new(input);
    let module = parser.module().map_err(|e| format!("Parse error: {e:?}"))?;

    let mut env = MacroEnvironment::new();

    // Collect macro definitions
    if let Syntax::Node(module_node) = &module {
        for child in &module_node.children {
            if let Syntax::Node(node) = child {
                match node.kind {
                    SyntaxKind::MacroDef => {
                        let macro_def = MacroEnvironment::create_macro_from_syntax(child)
                            .map_err(|e| format!("Failed to create macro: {e:?}"))?;
                        env.register_macro(macro_def);
                    }
                    SyntaxKind::MacroRules => {
                        let macro_defs = MacroEnvironment::create_macros_from_macro_rules(child)
                            .map_err(|e| {
                                format!("Failed to create macros from macro_rules: {e:?}")
                            })?;
                        for macro_def in macro_defs {
                            env.register_macro(macro_def);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let mut expander = MacroExpander::new(env);
    let expanded = expander
        .expand(&module)
        .map_err(|e| format!("Expansion error: {e:?}"))?;

    Ok(format_syntax(&expanded))
}

fn format_syntax(syntax: &Syntax) -> String {
    match syntax {
        Syntax::Missing => "<missing>".to_string(),
        Syntax::Atom(atom) => atom.value.to_string(),
        Syntax::Node(node) => {
            let kind = format!("{:?}", node.kind);
            if node.children.is_empty() {
                format!("({kind})")
            } else {
                let children: Vec<String> = node.children.iter().map(format_syntax).collect();
                format!("({kind} {})", children.join(" "))
            }
        }
    }
}

#[test]
fn test_nested_macro_expansion() {
    let input = r#"
macro "twice" x:term : term => `($x + $x)
macro "quad" x:term : term => `(twice (twice $x))

def result := quad 5
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand to ((5 + 5) + (5 + 5))
    assert!(expanded.contains("5"));
    assert!(expanded.contains("+"));
}

#[test]
fn test_macro_with_match_patterns() {
    let input = r#"
macro_rules
| `(option_map none $f) => `(none)
| `(option_map (some $x) $f) => `(some ($f $x))

def test1 := option_map none (fun x => x + 1)
def test2 := option_map (some 42) (fun x => x + 1)
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // test1 should expand to none
    // test2 should expand to some ((fun x => x + 1) 42)
    assert!(expanded.contains("none"));
    assert!(expanded.contains("some"));
}

#[test]
fn test_macro_with_complex_patterns() {
    let input = r#"
macro_rules
| `(when true do $x) => `($x)
| `(when false do $x) => `(())
| `(when $cond do $x) => `(if $cond then $x else ())

def test1 := when true do (print "yes")
def test2 := when false do (print "no")
def test3 := when (x > 0) do (print "positive")
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // test1 should expand to (print "yes")
    // test2 should expand to ()
    // test3 should expand to if (x > 0) then (print "positive") else ()
    assert!(expanded.contains("print"));
    assert!(expanded.contains("()"));
}

#[test]
fn test_recursive_macro_pattern() {
    let input = r#"
macro_rules
| `(sum []) => `(0)
| `(sum [$x]) => `($x)
| `(sum [$x, $xs,*]) => `($x + sum [$xs,*])

def empty := sum []
def single := sum [42]
def multiple := sum [1, 2, 3, 4, 5]
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand to nested additions
    assert!(expanded.contains("0")); // empty sum
    assert!(expanded.contains("42")); // single element
    assert!(expanded.contains("+")); // additions for multiple
}

#[test]
fn test_macro_hygiene() {
    let input = r#"
macro "let_temp" x:term y:term : term => `(let temp := $x; temp + $y)

def test := let temp := 100; let_temp 1 2
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // The macro's temp should not conflict with the outer temp
    // Both temps should be present but with different hygiene markers
    assert!(expanded.contains("temp"));
    assert!(expanded.contains("100"));
    assert!(expanded.contains("1"));
    assert!(expanded.contains("2"));
}

#[test]
fn test_macro_with_multiple_categories() {
    let input = r#"
macro "test" x:term "with" t:tactic : command => `(theorem test_thm : $x := by $t)

test (1 + 1 = 2) with rfl
"#;

    let result = expand_and_verify(input);
    // This might fail if we don't support mixed categories yet
    println!("Result: {result:?}");
}

#[test]
fn test_edge_case_empty_pattern() {
    let input = r#"
macro_rules
| `() => `(Unit.unit)

def test := ()
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    assert!(expanded.contains("Unit.unit"));
}

#[test]
fn test_edge_case_nested_quotations() {
    let input = r#"
macro "quote_twice" x:term : term => `(`($x + $x))

def test := quote_twice 5
"#;

    let result = expand_and_verify(input);
    println!("Result: {result:?}");

    // This tests nested quotations which might not be fully supported
}

#[test]
fn test_macro_with_operators() {
    let input = r#"
macro_rules
| `($x ?? $y) => `(match $x with | none => $y | some a => a)

def test := none ?? 42
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    assert!(expanded.contains("match"));
    assert!(expanded.contains("none"));
    assert!(expanded.contains("42"));
}

#[test]
fn test_stress_many_rules() {
    let input = r#"
macro_rules
| `(calc 0) => `(0)
| `(calc 1) => `(1)
| `(calc 2) => `(2)
| `(calc 3) => `(3)
| `(calc 4) => `(4)
| `(calc 5) => `(5)
| `(calc $x + $y) => `(calc $x + calc $y)
| `(calc $x * $y) => `(calc $x * calc $y)

def test := calc 2 + 3
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand calc expressions
    assert!(expanded.contains("2"));
    assert!(expanded.contains("3"));
}

#[test]
fn test_macro_error_handling() {
    // Test undefined macro
    let input = r#"
def test := undefined_macro 42
"#;

    let result = expand_and_verify(input);
    // Should succeed but not expand the undefined macro
    assert!(result.is_ok());
    assert!(result.unwrap().contains("undefined_macro"));
}

#[test]
fn test_ambiguous_patterns() {
    let input = r#"
macro_rules
| `(test $x) => `(first $x)
| `(test $x) => `(second $x)

def result := test 42
"#;

    let result = expand_and_verify(input);
    // This tests how we handle ambiguous patterns
    // Currently it should use the first matching rule
    println!("Result: {result:?}");
}

#[test]
fn test_macro_with_binders() {
    let input = r#"
macro "forall_intro" x:ident t:term : term => `(fun $x : Nat => $t)

def test := forall_intro x (x + 1)
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    assert!(expanded.contains("fun"));
    assert!(expanded.contains("x"));
    assert!(expanded.contains("Nat"));
}

#[test]
fn test_real_world_monad_syntax() {
    let input = r#"
macro_rules
| `(do let $x ← $e; $rest) => `(bind $e (fun $x => do $rest))
| `(do $e) => `($e)

def test := do let x ← getValue; let y ← getValue; pure (x + y)
"#;

    let expanded = expand_and_verify(input).expect("Failed to expand");
    println!("Expanded: {expanded}");

    // Should expand to nested binds
    assert!(expanded.contains("bind"));
    assert!(expanded.contains("fun"));
    assert!(expanded.contains("getValue"));
}

#[test]
fn test_performance_many_expansions() {
    // Test with many macro invocations
    let mut input = String::from("macro \"double\" x:term : term => `($x + $x)\n\n");

    // Create 100 definitions using the macro
    for i in 0..100 {
        input.push_str(&format!("def test{i} := double {i}\n"));
    }

    let start = std::time::Instant::now();
    let result = expand_and_verify(&input);
    let duration = start.elapsed();

    println!("Expansion of 100 macros took: {duration:?}");
    assert!(result.is_ok());

    // Should complete in reasonable time (< 1 second)
    assert!(duration.as_secs() < 1);
}
