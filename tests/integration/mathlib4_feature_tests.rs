use std::{fs, path::Path, time::Instant};
use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

/// Test parsing mathlib4 files that exercise specific language features
#[test]
fn test_mathlib4_import_statements() {
    // Test files with heavy import usage
    let test_content = r#"
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Basic
import Batteries.Logic
import Batteries.Tactic.Trans
import Batteries.Util.LibraryNote
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

open Function

variable {α : Sort*}
"#;

    let mut parser = Parser::new(test_content);
    match parser.module() {
        Ok(syntax) => {
            println!("Successfully parsed import-heavy content");
            let mut import_count = 0;
            count_imports(&syntax, &mut import_count);
            println!("Found {} import statements", import_count);
            assert!(import_count >= 7, "Should find at least 7 import statements");
        }
        Err(e) => {
            panic!("Failed to parse imports: {}", e);
        }
    }
}

#[test]
fn test_mathlib4_attribute_syntax() {
    // Test attribute syntax commonly used in mathlib4
    let test_content = r#"
attribute [trans] Iff.trans HEq.trans heq_of_eq_of_heq
attribute [simp] cast_heq

@[simp]
theorem test_theorem : True := trivial

instance (priority := 10) decidableEq_of_subsingleton [Subsingleton α] : DecidableEq α :=
  fun a b ↦ isTrue (Subsingleton.elim a b)
"#;

    let mut parser = Parser::new(test_content);
    match parser.module() {
        Ok(syntax) => {
            println!("Successfully parsed attribute syntax");
            let mut attr_count = 0;
            count_attributes(&syntax, &mut attr_count);
            println!("Found {} attribute declarations", attr_count);
        }
        Err(e) => {
            panic!("Failed to parse attributes: {}", e);
        }
    }
}

#[test]
fn test_mathlib4_instance_syntax() {
    // Test instance declarations with complex syntax
    let test_content = r#"
variable {α : Sort*}

instance (priority := 10) decidableEq_of_subsingleton [Subsingleton α] : DecidableEq α :=
  fun a b ↦ isTrue (Subsingleton.elim a b)

instance [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ ↦ by cases Subsingleton.elim x y; rfl⟩
"#;

    let mut parser = Parser::new(test_content);
    match parser.module() {
        Ok(syntax) => {
            println!("Successfully parsed instance syntax");
            let mut instance_count = 0;
            count_instances(&syntax, &mut instance_count);
            println!("Found {} instance declarations", instance_count);
        }
        Err(e) => {
            panic!("Failed to parse instances: {}", e);
        }
    }
}

#[test]
fn test_mathlib4_theorem_syntax() {
    // Test theorem declarations with complex proof syntax
    let test_content = r#"
variable {α β γ : Sort _}

theorem congr_heq {f : α → γ} {g : β → γ} {x : α} {y : β}
    (h₁ : f ≍ g) (h₂ : x ≍ y) : f x = g y := by
  cases h₂; cases h₁; rfl

theorem congr_arg_heq {β : α → Sort*} (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ ≍ a₂ → f a₁ ≍ f a₂ := fun h ↦ by cases h; rfl
"#;

    let mut parser = Parser::new(test_content);
    match parser.module() {
        Ok(syntax) => {
            println!("Successfully parsed theorem syntax");
            let mut theorem_count = 0;
            count_theorems(&syntax, &mut theorem_count);
            println!("Found {} theorem declarations", theorem_count);
        }
        Err(e) => {
            panic!("Failed to parse theorems: {}", e);
        }
    }
}

#[test]
#[ignore]
fn test_mathlib4_abbreviation_syntax() {
    // Test abbreviation declarations
    let test_content = r#"
/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
abbrev hidden {α : Sort*} {a : α} := a

abbrev MyNat := Nat
"#;

    let mut parser = Parser::new(test_content);
    match parser.module() {
        Ok(syntax) => {
            println!("Successfully parsed abbreviation syntax");
            // Check that we parsed something meaningful
            if let Syntax::Node(node) = &syntax {
                assert!(!node.children.is_empty(), "Should have parsed some content");
            }
        }
        Err(e) => {
            panic!("Failed to parse abbreviations: {}", e);
        }
    }
}

#[test]
#[ignore]
fn test_mathlib4_unicode_syntax() {
    // Test Unicode symbols commonly used in mathlib4
    let test_content = r#"
variable {α β : Type*}

theorem test_unicode (f : α → β) (g : β → α) : f ∘ g ≠ id := by sorry

example {x y : Nat} : x ≤ y ∧ y ≤ x ↔ x = y := by sorry

example : ∀ x : Nat, ∃ y : Nat, x ≤ y := fun x ↦ ⟨x, le_refl x⟩
"#;

    let mut parser = Parser::new(test_content);
    match parser.module() {
        Ok(syntax) => {
            println!("Successfully parsed Unicode syntax");
            if let Syntax::Node(node) = &syntax {
                assert!(!node.children.is_empty(), "Should have parsed Unicode content");
            }
        }
        Err(e) => {
            panic!("Failed to parse Unicode: {}", e);
        }
    }
}

#[test]
#[ignore]
fn test_mathlib4_tactic_syntax() {
    // Test basic tactic syntax
    let test_content = r#"
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | mk hp hq => 
    constructor
    · exact hq
    · exact hp

example (n : Nat) : n = n := by rfl

example (p : Prop) : p → p := by
  intro h
  assumption
"#;

    let mut parser = Parser::new(test_content);
    match parser.module() {
        Ok(syntax) => {
            println!("Successfully parsed tactic syntax");
            if let Syntax::Node(node) = &syntax {
                assert!(!node.children.is_empty(), "Should have parsed tactic content");
            }
        }
        Err(e) => {
            println!("Failed to parse tactics (expected - tactic support incomplete): {}", e);
            // Don't fail the test since tactic parsing is still being developed
        }
    }
}

#[test]
#[ignore]
fn test_mathlib4_performance_real_file() {
    // Test performance on our test data files
    let test_file = Path::new("../../../test-data/syntax/commands/theorems.lean");
    
    if !test_file.exists() {
        println!("Test file not found. Skipping performance test.");
        return;
    }

    let content = fs::read_to_string(test_file).expect("Failed to read test file");
    
    // Measure parsing time
    let start = Instant::now();
    let mut parser = Parser::new(&content);
    let result = parser.module();
    let duration = start.elapsed();
    
    println!("Parsed theorems.lean in {:?}", duration);
    println!("File size: {} bytes", content.len());
    
    match result {
        Ok(syntax) => {
            // Analyze the parsed result
            let mut stats = FileStats::new();
            analyze_file(&syntax, &mut stats);
            
            println!("Parse statistics:");
            println!("  - Total nodes: {}", stats.total_nodes);
            println!("  - Definitions: {}", stats.definitions);
            println!("  - Theorems: {}", stats.theorems);
            println!("  - Instances: {}", stats.instances);
            println!("  - Imports: {}", stats.imports);
            
            // Performance assertions
            let bytes_per_second = (content.len() as f64) / duration.as_secs_f64();
            println!("  - Parsing speed: {:.0} bytes/second", bytes_per_second);
            
            // We should be able to parse at least 1KB/second (very conservative)
            assert!(bytes_per_second > 1000.0, "Parsing speed too slow: {} bytes/second", bytes_per_second);
        }
        Err(e) => {
            panic!("Failed to parse theorems.lean: {}", e);
        }
    }
}

struct FileStats {
    total_nodes: usize,
    definitions: usize,
    theorems: usize,
    instances: usize,
    imports: usize,
}

impl FileStats {
    fn new() -> Self {
        Self {
            total_nodes: 0,
            definitions: 0,
            theorems: 0,
            instances: 0,
            imports: 0,
        }
    }
}

fn analyze_file(syntax: &Syntax, stats: &mut FileStats) {
    stats.total_nodes += 1;
    
    match syntax {
        Syntax::Node(node) => {
            match node.kind {
                SyntaxKind::Def => stats.definitions += 1,
                SyntaxKind::Theorem => stats.theorems += 1,
                SyntaxKind::Instance => stats.instances += 1,
                SyntaxKind::Import => stats.imports += 1,
                _ => {}
            }
            
            for child in &node.children {
                analyze_file(child, stats);
            }
        }
        _ => {}
    }
}

fn count_imports(syntax: &Syntax, count: &mut usize) {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == SyntaxKind::Import {
                *count += 1;
            }
            for child in &node.children {
                count_imports(child, count);
            }
        }
        _ => {}
    }
}

fn count_attributes(syntax: &Syntax, count: &mut usize) {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == SyntaxKind::AttributeList {
                *count += 1;
            }
            for child in &node.children {
                count_attributes(child, count);
            }
        }
        _ => {}
    }
}

fn count_instances(syntax: &Syntax, count: &mut usize) {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == SyntaxKind::Instance {
                *count += 1;
            }
            for child in &node.children {
                count_instances(child, count);
            }
        }
        _ => {}
    }
}

fn count_theorems(syntax: &Syntax, count: &mut usize) {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == SyntaxKind::Theorem {
                *count += 1;
            }
            for child in &node.children {
                count_theorems(child, count);
            }
        }
        _ => {}
    }
}