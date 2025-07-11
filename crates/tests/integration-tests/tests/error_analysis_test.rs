use std::{collections::HashMap, fs, path::Path};

use lean_parser::Parser;
use lean_syn_expr::{Syntax, SyntaxKind};

#[derive(Debug, Clone)]
struct ErrorContext {
    before: String,
    error: String,
    after: String,
    line: usize,
    file: String,
}

fn extract_error_contexts(
    syntax: &Syntax,
    source: &str,
    file_name: &str,
    errors: &mut Vec<ErrorContext>,
) {
    if let Syntax::Node(node) = syntax {
        if node.kind == SyntaxKind::Error {
            // Get position info
            let start = node.range.start.offset;
            let end = node.range.end.offset;

            // Extract context safely with UTF-8 boundaries
            let before_start = start.saturating_sub(50);
            let after_end = (end + 50).min(source.len());

            // Find valid UTF-8 boundaries
            let before_start = if before_start > 0 && !source.is_char_boundary(before_start) {
                let mut i = before_start;
                while i > 0 && !source.is_char_boundary(i) {
                    i -= 1;
                }
                i
            } else {
                before_start
            };

            let after_end = if after_end < source.len() && !source.is_char_boundary(after_end) {
                let mut i = after_end;
                while i < source.len() && !source.is_char_boundary(i) {
                    i += 1;
                }
                i
            } else {
                after_end
            };

            let before = source[before_start..start]
                .trim_start()
                .replace('\n', " ")
                .to_string();
            let error = source[start..end].replace('\n', " ").to_string();
            let after = source[end..after_end]
                .trim_end()
                .replace('\n', " ")
                .to_string();

            errors.push(ErrorContext {
                before,
                error,
                after,
                line: node.range.start.line as usize,
                file: file_name.to_string(),
            });
        }

        // Recurse
        for child in &node.children {
            extract_error_contexts(child, source, file_name, errors);
        }
    }
}

#[test]
fn analyze_parsing_errors() {
    let test_files = vec![
        "../../../test-data/implemented-features/Syntax/Basic/Comments.lean",
        "../../../test-data/implemented-features/Syntax/Basic/Identifiers.lean",
        "../../../test-data/implemented-features/Syntax/Basic/Literals.lean",
        "../../../test-data/implemented-features/Syntax/Commands/Definitions.lean",
        "../../../test-data/implemented-features/Syntax/Macros/BasicMacros.lean",
        "../../../test-data/implemented-features/Syntax/Macros/MacroExpansionSimple.lean",
    ];

    let mut all_errors = Vec::new();

    for file_path in &test_files {
        let path = Path::new(file_path);
        if !path.exists() {
            continue;
        }

        let content = fs::read_to_string(path).unwrap();
        let mut parser = Parser::new(&content);

        if let Ok(syntax) = parser.module() {
            let file_name = path.file_name().unwrap().to_str().unwrap();
            extract_error_contexts(&syntax, &content, file_name, &mut all_errors);
        }
    }

    // Group errors by pattern
    let mut error_patterns: HashMap<String, Vec<ErrorContext>> = HashMap::new();

    for error in &all_errors {
        // Create a pattern key
        let key = if error.error.contains("()") {
            "unit_type".to_string()
        } else if error.error.contains("←") {
            "bind_operator".to_string()
        } else if error.error.contains("do") {
            "do_notation".to_string()
        } else if error.error.contains("where") {
            "where_clause".to_string()
        } else if error.error.contains("·") {
            "cdot_operator".to_string()
        } else if error.error.trim().is_empty() {
            "empty".to_string()
        } else {
            "other".to_string()
        };

        error_patterns.entry(key).or_default().push(error.clone());
    }

    // Print analysis
    println!("\n=== Error Pattern Analysis ===\n");

    for (pattern, errors) in &error_patterns {
        println!("Pattern: {} (count: {})", pattern, errors.len());
        println!("{}", "-".repeat(60));

        // Show first 3 examples
        for (i, err) in errors.iter().take(3).enumerate() {
            println!("Example {} from {} line {}:", i + 1, err.file, err.line);
            println!("  Before: '{}'", err.before);
            println!("  Error:  '{}'", err.error);
            println!("  After:  '{}'", err.after);
            println!();
        }
    }

    println!("\nTotal errors found: {}", all_errors.len());
}

#[test]
fn test_specific_constructs() {
    let test_cases = vec![
        ("unit", "def x : Unit := ()"),
        (
            "bind_operator",
            "def test : IO Unit := do\n  let x ← getValue\n  return x",
        ),
        ("where_clause", "def f (x : Nat) where x > 0 := x"),
        ("cdot", "example : ∀ x, x = x := fun x => ·"),
        ("do_block", "def test := do\n  let x := 1\n  return x"),
    ];

    println!("\n=== Testing Specific Constructs ===\n");

    for (name, code) in test_cases {
        let mut parser = Parser::new(code);
        match parser.module() {
            Ok(syntax) => {
                let mut errors = Vec::new();
                extract_error_contexts(&syntax, code, name, &mut errors);

                if errors.is_empty() {
                    println!("{name}: ✅ PASSED");
                } else {
                    println!("{}: ❌ FAILED ({} errors)", name, errors.len());
                    for err in &errors {
                        println!("  Error: '{}'", err.error);
                    }
                }
            }
            Err(e) => {
                println!("{name}: ❌ PARSE ERROR: {e:?}");
            }
        }
    }
}
