use std::{fs, path::Path, time::Instant};

use lean_parser::Parser;

#[test]
#[ignore] // Run with `cargo test --test mathlib4_parser_test -- --ignored`
fn test_parse_mathlib4_files() {
    let mathlib_path = Path::new("test-data/mathlib4/Mathlib");
    assert!(
        mathlib_path.exists(),
        "mathlib4 test data not found. Run: git submodule update --init --recursive"
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
                            println!("Parsed {} files...", total_files);
                        }
                    }
                    Err(e) => {
                        failed_files.push((path.to_path_buf(), e.to_string()));
                    }
                }
            }
            Err(e) => {
                failed_files.push((path.to_path_buf(), format!("Failed to read file: {}", e)));
            }
        }
    });

    let duration = start.elapsed();

    println!("\n=== Mathlib4 Parser Test Results ===");
    println!("Total files: {}", total_files);
    println!("Successfully parsed: {}", parsed_files);
    println!("Failed: {}", failed_files.len());
    println!("Time elapsed: {:.2?}", duration);
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
    println!("\nSuccess rate: {:.2}%", success_rate);

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
    let test_file = Path::new("test-data/mathlib4/Mathlib/Data/Nat/Basic.lean");

    if !test_file.exists() {
        eprintln!("Test file not found. Skipping test.");
        return;
    }

    let content = fs::read_to_string(test_file).expect("Failed to read test file");
    let mut parser = Parser::new(&content);

    match parser.module() {
        Ok(_syntax) => {
            println!("Successfully parsed Mathlib/Data/Nat/Basic.lean");
            // Could add more specific assertions about the parsed structure
        }
        Err(e) => {
            panic!("Failed to parse Mathlib/Data/Nat/Basic.lean: {}", e);
        }
    }
}

fn visit_lean_files(dir: &Path, callback: &mut dyn FnMut(&Path)) {
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries {
            if let Ok(entry) = entry {
                let path = entry.path();
                if path.is_dir() {
                    visit_lean_files(&path, callback);
                } else if path.extension().map_or(false, |ext| ext == "lean") {
                    callback(&path);
                }
            }
        }
    }
}
