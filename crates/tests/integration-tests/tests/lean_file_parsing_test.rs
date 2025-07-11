use std::{fs, path::Path};

use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

fn parse_lean_file(path: &Path) -> Result<Syntax, String> {
    let content = fs::read_to_string(path).map_err(|e| format!("Failed to read file: {e}"))?;

    let mut parser = Parser::new(&content);
    parser.module().map_err(|e| format!("Parse error: {e:?}"))
}

fn count_nodes(syntax: &Syntax) -> (usize, usize, usize) {
    let mut total = 0;
    let mut errors = 0;
    let mut commands = 0;

    fn visit(syntax: &Syntax, total: &mut usize, errors: &mut usize, commands: &mut usize) {
        *total += 1;

        if let Syntax::Node(node) = syntax {
            if node.kind == SyntaxKind::Error {
                *errors += 1;
            }

            match node.kind {
                SyntaxKind::Def
                | SyntaxKind::Theorem
                | SyntaxKind::Instance
                | SyntaxKind::Structure
                | SyntaxKind::Inductive
                | SyntaxKind::Class
                | SyntaxKind::MacroDef
                | SyntaxKind::MacroRules => {
                    *commands += 1;
                }
                _ => {}
            }

            for child in &node.children {
                visit(child, total, errors, commands);
            }
        }
    }

    visit(syntax, &mut total, &mut errors, &mut commands);
    (total, errors, commands)
}

#[test]
fn test_parse_lean_test_files() {
    let test_files = [
        "../../../test-data/implemented-features/Syntax/Basic/Comments.lean",
        "../../../test-data/implemented-features/Syntax/Basic/Identifiers.lean",
        "../../../test-data/implemented-features/Syntax/Basic/Literals.lean",
        "../../../test-data/implemented-features/Syntax/Commands/Definitions.lean",
        "../../../test-data/implemented-features/Syntax/Expressions/Lambda.lean",
        "../../../test-data/implemented-features/Syntax/Macros/BasicMacros.lean",
        "../../../test-data/implemented-features/Syntax/Macros/MacroRules.lean",
    ];

    println!("\nParsing Lean test files:\n");
    println!(
        "{:<60} {:>10} {:>10} {:>10}",
        "File", "Total", "Errors", "Commands"
    );
    println!("{}", "-".repeat(100));

    let mut total_files = 0;
    let mut successful_files = 0;
    let mut total_errors = 0;

    for file_path in &test_files {
        let path = Path::new(file_path);
        if !path.exists() {
            println!("{file_path:<60} NOT FOUND");
            continue;
        }

        total_files += 1;

        match parse_lean_file(path) {
            Ok(syntax) => {
                let (total, errors, commands) = count_nodes(&syntax);
                println!(
                    "{:<60} {:>10} {:>10} {:>10}",
                    path.file_name().unwrap().to_str().unwrap(),
                    total,
                    errors,
                    commands
                );

                if errors == 0 {
                    successful_files += 1;
                }
                total_errors += errors;
            }
            Err(e) => {
                println!("{file_path:<60} PARSE ERROR: {e}");
            }
        }
    }

    println!("{}", "-".repeat(100));
    println!("\nSummary:");
    println!("  Files parsed: {successful_files}/{total_files}");
    println!("  Total errors: {total_errors}");
    println!(
        "  Success rate: {:.1}%",
        if total_files > 0 {
            (successful_files as f64 / total_files as f64) * 100.0
        } else {
            0.0
        }
    );
}

#[test]
fn test_parse_macro_expansion_files() {
    let macro_dir = Path::new("../../../test-data/implemented-features/Syntax/Macros");

    if !macro_dir.exists() {
        println!("Macro directory not found");
        return;
    }

    println!("\nParsing all macro files:\n");

    let mut results = Vec::new();

    for entry in fs::read_dir(macro_dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().and_then(|s| s.to_str()) == Some("lean") {
            let file_name = path.file_name().unwrap().to_str().unwrap().to_string();

            match parse_lean_file(&path) {
                Ok(syntax) => {
                    let (total, errors, commands) = count_nodes(&syntax);
                    results.push((file_name, true, total, errors, commands));
                }
                Err(e) => {
                    results.push((file_name, false, 0, 0, 0));
                    eprintln!("Failed to parse {}: {}", path.display(), e);
                }
            }
        }
    }

    // Sort by success, then by name
    results.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    println!(
        "{:<40} {:>10} {:>10} {:>10} {:>10}",
        "File", "Status", "Total", "Errors", "Commands"
    );
    println!("{}", "-".repeat(80));

    for (name, success, total, errors, commands) in &results {
        println!(
            "{:<40} {:>10} {:>10} {:>10} {:>10}",
            name,
            if *success { "OK" } else { "FAILED" },
            if *success {
                total.to_string()
            } else {
                "-".to_string()
            },
            if *success {
                errors.to_string()
            } else {
                "-".to_string()
            },
            if *success {
                commands.to_string()
            } else {
                "-".to_string()
            }
        );
    }

    let successful = results.iter().filter(|r| r.1).count();
    let total = results.len();

    println!("{}", "-".repeat(80));
    println!(
        "\nSuccess rate: {}/{} ({:.1}%)",
        successful,
        total,
        (successful as f64 / total as f64) * 100.0
    );
}
