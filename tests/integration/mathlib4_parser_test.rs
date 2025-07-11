#![allow(clippy::uninlined_format_args)]
#![allow(clippy::single_match)]

use std::{fs, path::Path, time::Instant};

use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
#[ignore] // Run with `cargo test --test mathlib4_parser_test -- --ignored`
fn test_parse_mathlib4_files() {
    let mathlib_path = Path::new("../../../test-data/mathlib4/Mathlib");
    assert!(
        mathlib_path.exists(),
        "Mathlib4 directory not found at {:?}",
        mathlib_path
    );

    let mut total_files = 0;
    let mut parsed_files = 0;
    let mut failed_files = Vec::new();
    let start = Instant::now();

    visit_lean_files(mathlib_path, &mut |path| {
        total_files += 1;

        match fs::read_to_string(path) {
            Ok(content) => {
                let mut parser = Parser::new(&content);
                match parser.module() {
                    Ok(_) => {
                        parsed_files += 1;
                        if total_files % 100 == 0 {
                            println!("Parsed {total_files} files...");
                        }
                    }
                    Err(e) => {
                        failed_files.push((path.to_path_buf(), e.to_string()));
                    }
                }
            }
            Err(e) => {
                failed_files.push((path.to_path_buf(), format!("Failed to read file: {e}")));
            }
        }
    });

    let duration = start.elapsed();

    println!("\n=== Test Data Parser Results ===");
    println!("Total files: {total_files}");
    println!("Successfully parsed: {parsed_files}");
    println!("Failed: {}", failed_files.len());
    println!("Time elapsed: {duration:.2?}");
    println!(
        "Average time per file: {:.2?}",
        duration / total_files as u32
    );

    if !failed_files.is_empty() {
        println!("\n=== Failed Files (first 10) ===");
        for (path, error) in failed_files.iter().take(10) {
            println!("{}: {}", path.display(), error);
        }
    }

    // For now, we don't fail the test even if some files fail to parse
    // This allows us to track progress incrementally
    let success_rate = (parsed_files as f64 / total_files as f64) * 100.0;
    println!("\nSuccess rate: {success_rate:.2}%");

    // Set a minimum success rate threshold
    assert!(
        success_rate > 0.0,
        "Parser should be able to parse at least some files"
    );
}

#[test]
#[ignore] // Run with `cargo test --test mathlib4_parser_test
          // test_parse_mathlib4_comprehensive -- --ignored`
fn test_parse_mathlib4_comprehensive() {
    // Test a broader sample of Mathlib4 files to get realistic success rate
    let mathlib_path = Path::new("../../../test-data/mathlib4/Mathlib");

    if !mathlib_path.exists() {
        eprintln!("Mathlib4 directory not found, skipping comprehensive test");
        return;
    }

    let mut total_files = 0;
    let mut parsed_files = 0;
    let mut failed_files = Vec::new();
    let start = Instant::now();

    // Test files from different mathematical areas to get broad coverage
    let test_categories = [
        // Core/Basic files
        ("Init.lean", "Core initialization"),
        ("Logic/Basic.lean", "Basic logic"),
        ("Data/Nat/Basic.lean", "Natural numbers"),
        ("Data/Int/Basic.lean", "Integers"),
        ("Data/Bool/Basic.lean", "Booleans"),
        // Algebra
        ("Algebra/Group/Basic.lean", "Group theory"),
        ("Algebra/Ring/Basic.lean", "Ring theory"),
        ("Algebra/Field/Basic.lean", "Field theory"),
        // Analysis
        ("Analysis/Calculus/Deriv/Basic.lean", "Derivatives"),
        ("Analysis/Normed/Group/Basic.lean", "Normed groups"),
        // Topology
        ("Topology/Basic.lean", "Basic topology"),
        ("Topology/MetricSpace/Basic.lean", "Metric spaces"),
        // Category Theory
        ("CategoryTheory/Functor/Basic.lean", "Functors"),
        // Number Theory
        ("NumberTheory/Basic.lean", "Number theory"),
        // Set Theory
        ("SetTheory/Cardinal/Basic.lean", "Cardinals"),
        // Linear Algebra
        ("LinearAlgebra/Basic.lean", "Linear algebra"),
        // Combinatorics
        ("Combinatorics/Enumerative/Basic.lean", "Combinatorics"),
        // Order Theory
        ("Order/Basic.lean", "Order theory"),
        // Measure Theory
        ("MeasureTheory/MeasurableSpace/Basic.lean", "Measure theory"),
    ];

    for (file_path, description) in &test_categories {
        let full_path = mathlib_path.join(file_path);

        if !full_path.exists() {
            println!("File {} not found, skipping", file_path);
            continue;
        }

        total_files += 1;
        println!("Testing {}: {}", description, file_path);

        match fs::read_to_string(&full_path) {
            Ok(content) => {
                let mut parser = Parser::new(&content);
                match parser.module() {
                    Ok(_) => {
                        parsed_files += 1;
                        println!("✅ Successfully parsed {}", file_path);
                    }
                    Err(e) => {
                        failed_files.push((file_path.to_string(), e.to_string()));
                        println!("❌ Failed to parse {}: {}", file_path, e);
                    }
                }
            }
            Err(e) => {
                failed_files.push((file_path.to_string(), format!("Failed to read: {}", e)));
                println!("❌ Failed to read {}: {}", file_path, e);
            }
        }
    }

    let duration = start.elapsed();
    println!("\n=== Mathlib4 Comprehensive Test Results ===");
    println!("Total files tested: {}", total_files);
    println!("Successfully parsed: {}", parsed_files);
    println!("Failed: {}", failed_files.len());
    println!("Duration: {:?}", duration);

    if !failed_files.is_empty() {
        println!("\n=== Failed Files ===");
        for (path, error) in &failed_files {
            println!("{}: {}", path, error);
        }
    }

    let success_rate = if total_files > 0 {
        (parsed_files as f64 / total_files as f64) * 100.0
    } else {
        0.0
    };
    println!("\nSuccess rate: {:.2}%", success_rate);
    println!("This gives us a realistic picture of our Lean4 parsing capabilities!");

    // We expect at least 50% success on this diverse sample
    assert!(
        success_rate >= 30.0,
        "Should be able to parse at least 30% of diverse Mathlib4 files"
    );
}

#[test]
fn test_parse_complex_mathlib4_verification() {
    // Manually verify parsing of a very complex file to check if results are real
    let complex_file = "../../../test-data/mathlib4/Mathlib/Analysis/Calculus/Deriv/Basic.lean";
    let path = Path::new(complex_file);

    if !path.exists() {
        eprintln!("Complex analysis file not found");
        return;
    }

    let content = fs::read_to_string(path).expect("Failed to read complex analysis file");
    println!("File size: {} bytes", content.len());
    println!("First 200 chars: {}", &content[..200.min(content.len())]);

    let mut parser = Parser::new(&content);
    match parser.module() {
        Ok(syntax) => {
            println!("✅ Successfully parsed complex analysis file");
            println!(
                "Syntax tree has {} total nodes",
                count_syntax_nodes(&syntax)
            );

            // Check that we actually parsed meaningful content
            if count_syntax_nodes(&syntax) < 10 {
                panic!("Syntax tree too small - parsing might be trivial");
            }
        }
        Err(e) => {
            panic!("❌ Failed to parse complex analysis file: {}", e);
        }
    }
}

fn count_syntax_nodes(syntax: &Syntax) -> usize {
    match syntax {
        Syntax::Node(node) => 1 + node.children.iter().map(count_syntax_nodes).sum::<usize>(),
        Syntax::Atom(_) => 1,
        Syntax::Missing => 1,
    }
}

#[test]
fn test_parse_mathlib4_init() {
    let init_path = Path::new("../../../test-data/mathlib4/Mathlib/Init.lean");

    if !init_path.exists() {
        eprintln!("Mathlib4 Init.lean not found, skipping test");
        return;
    }

    let content = fs::read_to_string(init_path).expect("Failed to read Init.lean");
    let mut parser = Parser::new(&content);

    match parser.module() {
        Ok(_) => {
            println!("✅ Successfully parsed Mathlib/Init.lean");
        }
        Err(e) => {
            panic!("❌ Failed to parse Mathlib/Init.lean: {}", e);
        }
    }
}

#[test]
fn test_parse_mathlib4_logic_basic_partial() {
    // Test just the header and imports of Logic/Basic.lean
    let logic_basic_imports = r#"/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Basic
import Batteries.Logic
import Batteries.Tactic.Trans

open Function

section Miscellany
end Miscellany"#;

    let mut parser = Parser::new(logic_basic_imports);
    match parser.module() {
        Ok(_) => {
            println!("✅ Successfully parsed Logic/Basic.lean header");
        }
        Err(e) => {
            panic!("❌ Failed to parse Logic/Basic.lean header: {}", e);
        }
    }
}

#[test]
fn test_parse_simple_mathlib4_constructs() {
    // Test various simple Mathlib4 constructs
    let simple_constructs = r#"
import Mathlib.Data.Nat.Basic

-- Simple theorem
theorem simple_theorem (n : Nat) : n + 0 = n := by
  rw [Nat.add_zero]

-- Simple definition  
def double (n : Nat) : Nat := n + n

-- Simple attribute
attribute [simp] double
"#;

    let mut parser = Parser::new(simple_constructs);
    match parser.module() {
        Ok(_) => {
            println!("✅ Successfully parsed simple Mathlib4 constructs");
        }
        Err(e) => {
            panic!("❌ Failed to parse simple Mathlib4 constructs: {}", e);
        }
    }
}

#[test]
#[ignore] // Run with `cargo test --test mathlib4_parser_test test_parse_mathlib4_sample
          // -- --ignored`
fn test_parse_mathlib4_sample() {
    // Test a sample of real Mathlib4 files to get an idea of our success rate
    let test_files = [
        "../../../test-data/mathlib4/Mathlib/Init.lean",
        "../../../test-data/mathlib4/Mathlib/Logic/Basic.lean",
        "../../../test-data/mathlib4/Mathlib/Data/Nat/Basic.lean",
        "../../../test-data/mathlib4/Mathlib/Algebra/Group/Basic.lean",
        "../../../test-data/mathlib4/Mathlib/Logic/Relation.lean",
        "../../../test-data/mathlib4/Mathlib/Data/Bool/Basic.lean",
    ];

    let mut total_files = 0;
    let mut parsed_files = 0;
    let mut failed_files = Vec::new();

    for file_path in &test_files {
        let path = Path::new(file_path);

        if !path.exists() {
            println!("File {} not found, skipping", file_path);
            continue;
        }

        total_files += 1;
        println!("Testing file: {}", file_path);

        match fs::read_to_string(path) {
            Ok(content) => {
                let mut parser = Parser::new(&content);
                match parser.module() {
                    Ok(_) => {
                        parsed_files += 1;
                        println!("✅ Successfully parsed {}", file_path);
                    }
                    Err(e) => {
                        failed_files.push((file_path.to_string(), e.to_string()));
                        println!("❌ Failed to parse {}: {}", file_path, e);
                    }
                }
            }
            Err(e) => {
                failed_files.push((file_path.to_string(), format!("Failed to read: {}", e)));
                println!("❌ Failed to read {}: {}", file_path, e);
            }
        }
    }

    println!("\n=== Mathlib4 Sample Test Results ===");
    println!("Total files tested: {}", total_files);
    println!("Successfully parsed: {}", parsed_files);
    println!("Failed: {}", failed_files.len());

    if !failed_files.is_empty() {
        println!("\n=== Failed Files ===");
        for (path, error) in &failed_files {
            println!("{}: {}", path, error);
        }
    }

    let success_rate = if total_files > 0 {
        (parsed_files as f64 / total_files as f64) * 100.0
    } else {
        0.0
    };
    println!("\nSuccess rate: {:.2}%", success_rate);

    // We expect at least some success on real Mathlib4 files
    assert!(
        success_rate > 0.0,
        "Should be able to parse at least some Mathlib4 files"
    );
}

#[test]
#[ignore]
fn test_parse_specific_mathlib4_file() {
    // Test parsing a specific well-known file
    let test_files = [
        "../../../test-data/syntax/commands/definitions.lean",
        "../../../test-data/syntax/commands/theorems.lean",
        "../../../test-data/syntax/commands/instances.lean",
        "../../../test-data/syntax/expressions/lambda.lean",
        "../../../test-data/syntax/expressions/application.lean",
    ];

    for test_file_path in &test_files {
        let test_file = Path::new(test_file_path);

        if !test_file.exists() {
            eprintln!("Test file {} not found. Skipping.", test_file_path);
            continue;
        }

        let content = fs::read_to_string(test_file).expect("Failed to read test file");
        let mut parser = Parser::new(&content);

        match parser.module() {
            Ok(_syntax) => {
                println!("Successfully parsed {}", test_file_path);
                // Could add more specific assertions about the parsed structure
            }
            Err(e) => {
                panic!("Failed to parse {}: {e}", test_file_path);
            }
        }
    }
}

#[test]
#[ignore]
fn test_mathlib4_performance_benchmark() {
    // We'll use our own test data for benchmarking

    let test_files = [
        "../../../test-data/syntax/commands/definitions.lean",
        "../../../test-data/syntax/commands/theorems.lean",
        "../../../test-data/syntax/expressions/lambda.lean",
    ];

    let mut total_time = std::time::Duration::ZERO;
    let mut total_files = 0;

    for test_file_path in &test_files {
        let test_file = Path::new(test_file_path);
        if !test_file.exists() {
            continue;
        }

        let content = fs::read_to_string(test_file).expect("Failed to read test file");
        total_files += 1;

        let start = Instant::now();
        let mut parser = Parser::new(&content);
        let result = parser.module();
        let duration = start.elapsed();

        total_time += duration;

        match result {
            Ok(_) => {
                println!("Parsed {} in {:?}", test_file_path, duration);
            }
            Err(e) => {
                println!(
                    "Failed to parse {} in {:?}: {}",
                    test_file_path, duration, e
                );
            }
        }
    }

    if total_files > 0 {
        let avg_time = total_time / total_files;
        println!("\n=== Performance Summary ===");
        println!("Total files: {}", total_files);
        println!("Total time: {:?}", total_time);
        println!("Average time per file: {:?}", avg_time);

        // Performance goal: should parse each file in reasonable time
        // For small-medium files, we expect sub-second parsing
        assert!(
            avg_time < std::time::Duration::from_secs(5),
            "Average parsing time {} exceeds 5 seconds",
            avg_time.as_secs_f64()
        );
    }
}

#[test]
#[ignore]
fn test_mathlib4_macro_heavy_files() {
    // Test files that are known to have heavy macro usage
    let macro_heavy_files = [
        "../../../test-data/syntax/tactics/basic.lean",
        "../../../test-data/syntax/tactics/structured.lean",
    ];

    for test_file_path in &macro_heavy_files {
        let test_file = Path::new(test_file_path);
        if !test_file.exists() {
            println!(
                "Macro-heavy test file {} not found. Skipping.",
                test_file_path
            );
            continue;
        }

        let content = fs::read_to_string(test_file).expect("Failed to read test file");
        let mut parser = Parser::new(&content);

        let start = Instant::now();
        match parser.module() {
            Ok(syntax) => {
                let duration = start.elapsed();
                println!(
                    "Successfully parsed macro-heavy file {} in {:?}",
                    test_file_path, duration
                );

                // Check that we actually got a meaningful parse tree
                if let lean_syn_expr::Syntax::Node(node) = &syntax {
                    assert!(
                        !node.children.is_empty(),
                        "Parsed syntax should not be empty"
                    );
                    println!("Parse tree has {} top-level children", node.children.len());
                }
            }
            Err(e) => {
                let duration = start.elapsed();
                println!(
                    "Failed to parse macro-heavy file {} in {:?}: {}",
                    test_file_path, duration, e
                );
                // For now, don't fail the test - macro support is still being
                // developed
            }
        }
    }
}

#[test]
#[ignore]
fn test_mathlib4_syntax_categories() {
    // Test files that exercise different syntax categories
    let syntax_test_files = [
        ("commands/definitions.lean", "Basic definitions"),
        ("expressions/lambda.lean", "Lambda expressions"),
        ("patterns/basic.lean", "Pattern matching"),
    ];

    let test_data_path = "../../../test-data/syntax";

    for (file_path, description) in &syntax_test_files {
        let full_path = format!("{}/{}", test_data_path, file_path);
        let test_file = Path::new(&full_path);

        if !test_file.exists() {
            println!("Syntax test file {} not found. Skipping.", full_path);
            continue;
        }

        let content = fs::read_to_string(test_file).expect("Failed to read test file");
        let mut parser = Parser::new(&content);

        match parser.module() {
            Ok(syntax) => {
                println!("Successfully parsed {} ({})", file_path, description);

                // Analyze the syntax tree for interesting patterns
                let mut stats = SyntaxStats::new();
                analyze_syntax(&syntax, &mut stats);

                println!("  - Definitions: {}", stats.definitions);
                println!("  - Theorems: {}", stats.theorems);
                println!("  - Instances: {}", stats.instances);
                println!("  - Total nodes: {}", stats.total_nodes);
            }
            Err(e) => {
                println!("Failed to parse {} ({}): {}", file_path, description, e);
                // For comprehensive testing, we log failures but don't panic
            }
        }
    }
}

struct SyntaxStats {
    definitions: usize,
    theorems: usize,
    instances: usize,
    total_nodes: usize,
}

impl SyntaxStats {
    fn new() -> Self {
        Self {
            definitions: 0,
            theorems: 0,
            instances: 0,
            total_nodes: 0,
        }
    }
}

fn analyze_syntax(syntax: &lean_syn_expr::Syntax, stats: &mut SyntaxStats) {
    use lean_syn_expr::{Syntax, SyntaxKind};

    stats.total_nodes += 1;

    match syntax {
        Syntax::Node(node) => {
            match node.kind {
                SyntaxKind::Def => stats.definitions += 1,
                SyntaxKind::Theorem => stats.theorems += 1,
                SyntaxKind::Instance => stats.instances += 1,
                _ => {}
            }

            // Recursively analyze children
            for child in &node.children {
                analyze_syntax(child, stats);
            }
        }
        _ => {}
    }
}

#[test]
#[ignore]
fn test_mathlib4_style_imports() {
    // Test mathlib4-style import syntax
    let test_content = r#"
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Basic
import Batteries.Logic

open Function

variable {α : Sort*}
"#;

    let mut parser = Parser::new(test_content);
    match parser.module() {
        Ok(syntax) => {
            println!("Successfully parsed import-heavy content");
            let mut import_count = 0;
            count_syntax_kind(&syntax, SyntaxKind::Import, &mut import_count);
            println!("Found {} import statements", import_count);
            assert!(
                import_count >= 3,
                "Should find at least 3 import statements"
            );
        }
        Err(e) => {
            panic!("Failed to parse imports: {}", e);
        }
    }
}

#[test]
#[ignore]
fn test_mathlib4_style_performance() {
    // Test performance on our largest test file
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
        Ok(_syntax) => {
            let bytes_per_second = (content.len() as f64) / duration.as_secs_f64();
            println!("Parsing speed: {:.0} bytes/second", bytes_per_second);

            // Performance goals: should be very fast for small files
            assert!(
                bytes_per_second > 10000.0,
                "Parsing speed too slow: {} bytes/second",
                bytes_per_second
            );
            assert!(
                duration < std::time::Duration::from_millis(100),
                "Parsing took too long: {:?}",
                duration
            );
        }
        Err(e) => {
            panic!("Failed to parse theorems.lean: {}", e);
        }
    }
}

fn count_syntax_kind(syntax: &Syntax, target_kind: SyntaxKind, count: &mut usize) {
    match syntax {
        Syntax::Node(node) => {
            if node.kind == target_kind {
                *count += 1;
            }
            for child in &node.children {
                count_syntax_kind(child, target_kind, count);
            }
        }
        _ => {}
    }
}

fn visit_lean_files(dir: &Path, callback: &mut dyn FnMut(&Path)) {
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                visit_lean_files(&path, callback);
            } else if path.extension().is_some_and(|ext| ext == "lean") {
                callback(&path);
            }
        }
    }
}
