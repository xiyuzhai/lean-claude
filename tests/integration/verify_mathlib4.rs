#![allow(clippy::uninlined_format_args)]

use std::{fs, path::Path};
use lean_parser::Parser;

#[test]
fn verify_complex_mathlib4_files() {
    // Test some of the most complex files to verify our parsing
    let test_files = [
        ("test-data/mathlib4/Mathlib/Analysis/Calculus/Deriv/Basic.lean", "Complex analysis"),
        ("test-data/mathlib4/Mathlib/CategoryTheory/Functor/Basic.lean", "Category theory"),
        ("test-data/mathlib4/Mathlib/Algebra/Ring/Basic.lean", "Ring theory"),
        ("test-data/mathlib4/Mathlib/Topology/Basic.lean", "Topology"),
        ("test-data/mathlib4/Mathlib/NumberTheory/Basic.lean", "Number theory"),
    ];
    
    for (file_path, description) in &test_files {
        let path = Path::new(&format!("../../../{}", file_path));
        
        if !path.exists() {
            println!("File {} not found", file_path);
            continue;
        }
        
        println!("Testing {}: {}", description, file_path);
        
        let content = fs::read_to_string(path).expect("Failed to read file");
        println!("File size: {} bytes", content.len());
        
        let mut parser = Parser::new(&content);
        match parser.module() {
            Ok(syntax) => {
                println!("✅ Successfully parsed {} (syntax tree has {} nodes)", 
                        file_path, count_syntax_nodes(&syntax));
            }
            Err(e) => {
                println!("❌ Failed to parse {}: {}", file_path, e);
                panic!("Expected to parse this file successfully");
            }
        }
    }
}

fn count_syntax_nodes(syntax: &lean_syn_expr::Syntax) -> usize {
    match syntax {
        lean_syn_expr::Syntax::Node(node) => {
            1 + node.children.iter().map(count_syntax_nodes).sum::<usize>()
        }
        lean_syn_expr::Syntax::Atom(_) => 1,
        lean_syn_expr::Syntax::Missing(_) => 1,
    }
}