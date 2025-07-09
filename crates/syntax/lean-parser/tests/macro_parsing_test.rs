use std::{fs, path::Path};

use lean_parser::Parser;

fn parse_macro_file(path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let content = fs::read_to_string(path)?;
    let mut parser = Parser::new(&content);
    let result = parser.module();

    match result {
        Ok(_module) => {
            println!("✓ Successfully parsed: {path}");
            Ok(())
        }
        Err(err) => {
            eprintln!("✗ Failed to parse {path}: {err:?}");
            Err(format!("Parse error in {path}: {err:?}").into())
        }
    }
}

#[test]
fn test_parse_basic_macros() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../test-data/syntax/macros/basic_macros.lean");

    parse_macro_file(path.to_str().unwrap()).unwrap();
}

#[test]
fn test_parse_macro_rules() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../test-data/syntax/macros/macro_rules.lean");

    parse_macro_file(path.to_str().unwrap()).unwrap();
}

#[test]
fn test_parse_notation() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../test-data/syntax/macros/notation.lean");

    parse_macro_file(path.to_str().unwrap()).unwrap();
}

#[test]
fn test_parse_syntax_declarations() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../test-data/syntax/macros/syntax_declarations.lean");

    parse_macro_file(path.to_str().unwrap()).unwrap();
}

#[test]
#[ignore = "Syntax quotations require more implementation"]
fn test_parse_syntax_quotations() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../test-data/syntax/macros/syntax_quotations.lean");

    parse_macro_file(path.to_str().unwrap()).unwrap();
}

#[test]
#[ignore = "Advanced macros require full implementation"]
fn test_parse_advanced_macros() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../test-data/syntax/macros/advanced_macros.lean");

    parse_macro_file(path.to_str().unwrap()).unwrap();
}

#[test]
#[ignore = "Elaboration macros require elaborator support"]
fn test_parse_elab_macros() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../test-data/syntax/macros/elab_macros.lean");

    parse_macro_file(path.to_str().unwrap()).unwrap();
}

#[test]
fn test_all_macro_files() {
    let macro_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../test-data/syntax/macros");

    let mut total = 0;
    let mut passed = 0;

    if let Ok(entries) = fs::read_dir(&macro_dir) {
        for entry in entries.flatten() {
            if let Some(ext) = entry.path().extension() {
                if ext == "lean" {
                    total += 1;
                    let path = entry.path();
                    let path_str = path.to_str().unwrap();

                    // Skip known complex files
                    if path_str.contains("syntax_quotations")
                        || path_str.contains("advanced_macros")
                        || path_str.contains("elab_macros")
                    {
                        println!("⚠ Skipping complex file: {path_str}");
                        continue;
                    }

                    if parse_macro_file(path_str).is_ok() {
                        passed += 1;
                    }
                }
            }
        }
    }

    println!("\nMacro parsing test summary: {passed}/{total} files passed");
    assert!(
        passed >= 4,
        "Expected at least 4 macro files to parse successfully"
    );
}
