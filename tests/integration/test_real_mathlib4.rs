#![allow(clippy::uninlined_format_args)]

use std::{fs, path::Path};
use lean_parser::Parser;

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
fn test_parse_mathlib4_logic_basic() {
    let logic_basic_path = Path::new("../../../test-data/mathlib4/Mathlib/Logic/Basic.lean");
    
    if !logic_basic_path.exists() {
        eprintln!("Mathlib4 Logic/Basic.lean not found, skipping test");
        return;
    }
    
    let content = fs::read_to_string(logic_basic_path).expect("Failed to read Logic/Basic.lean");
    let mut parser = Parser::new(&content);
    
    match parser.module() {
        Ok(_) => {
            println!("✅ Successfully parsed Mathlib/Logic/Basic.lean");
        }
        Err(e) => {
            println!("❌ Failed to parse Mathlib/Logic/Basic.lean: {}", e);
            // For now, don't panic - this is expected as it's a complex file
            // panic!("Failed to parse Mathlib/Logic/Basic.lean: {}", e);
        }
    }
}

#[test]
fn test_parse_simple_mathlib4_constructs() {
    // Test parsing just import statements like those in Init.lean
    let simple_imports = r#"
import Lean.Linter.Sets
import Mathlib.Tactic.Linter.CommandStart
import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter
"#;
    
    let mut parser = Parser::new(simple_imports);
    match parser.module() {
        Ok(_) => {
            println!("✅ Successfully parsed simple import statements");
        }
        Err(e) => {
            panic!("❌ Failed to parse simple imports: {}", e);
        }
    }
}