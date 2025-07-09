// Macro Expansion Demo - Run with lean-parser
// This file demonstrates actual macro expansion using the Lean parser

use lean_parser::ExpandingParser;
use lean_syn_expr::Syntax;

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
                format!("({} {})", kind, children.join(" "))
            }
        }
    }
}

fn demonstrate_expansion(name: &str, input: &str) {
    println!("\n=== {} ===", name);
    println!("Input:\n{}", input.trim());
    
    let mut parser = ExpandingParser::new(input);
    match parser.parse_module() {
        Ok(expanded) => {
            println!("\nExpanded AST:\n{}", format_syntax(&expanded));
        }
        Err(e) => {
            println!("\nError: {:?}", e);
        }
    }
    println!("\n{}", "=".repeat(50));
}

fn main() {
    // Example 1: Simple value replacement
    demonstrate_expansion(
        "Simple Value Macro",
        r#"
macro "myNumber" : term => `(42)
def x := myNumber
"#
    );

    // Example 2: Single parameter substitution
    demonstrate_expansion(
        "Parameter Substitution",
        r#"
macro "double" x:term : term => `($x + $x)
def result := double 21
"#
    );

    // Example 3: Nested macro expansion
    demonstrate_expansion(
        "Nested Macros",
        r#"
macro "double" x:term : term => `($x + $x)
macro "quad" x:term : term => `(double (double $x))
def result := quad 5
"#
    );

    // Example 4: Multiple uses
    demonstrate_expansion(
        "Multiple Macro Uses",
        r#"
macro "inc" x:term : term => `($x + 1)
def a := inc 1
def b := inc (inc 2)
def c := inc (inc (inc 3))
"#
    );

    // Example 5: Complex expressions
    demonstrate_expansion(
        "Complex Expression",
        r#"
macro "assert!" cond:term : term => `(if $cond then () else panic!)
def test := assert! (1 < 2)
"#
    );

    // Example 6: Binary operator style
    demonstrate_expansion(
        "Binary Operator Macro",
        r#"
macro:50 x:term " ** " y:term : term => `(Nat.pow $x $y)
def result := 2 ** 8
"#
    );

    // Example 7: Multiple parameters
    demonstrate_expansion(
        "Multiple Parameters",
        r#"
macro "ite" cond:term "?" t:term ":" f:term : term => `(if $cond then $t else $f)
def result := ite true ? 100 : 200
"#
    );

    // Example 8: Demonstrating hygiene
    demonstrate_expansion(
        "Hygienic Expansion",
        r#"
macro "with_temp" body:term : term => `(let tmp := 42; $body)
def x := with_temp (tmp + 1)
def y := let tmp := 100; with_temp (tmp + 1)
"#
    );
}

// To run this demo:
// cargo run --example expansion_demo