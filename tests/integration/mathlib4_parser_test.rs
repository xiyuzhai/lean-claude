#![allow(clippy::uninlined_format_args)]
#![allow(clippy::single_match)]

use std::{fs, path::Path, time::Instant};

use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[test]
#[ignore] // Run with `cargo test --test mathlib4_parser_test -- --ignored`
fn test_parse_mathlib4_files() {
    let test_data_path = Path::new("../../../test-data/syntax");
    assert!(
        test_data_path.exists(),
        "test data not found at {:?}",
        test_data_path
    );

    let mut total_files = 0;
    let mut parsed_files = 0;
    let mut failed_files = Vec::new();
    let start = Instant::now();

    visit_lean_files(test_data_path, &mut |path| {
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
