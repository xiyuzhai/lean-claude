use std::fs;
use std::path::{Path, PathBuf};
use lean_parser::Parser;

#[test]
fn test_all_syntax_files() {
    // Find test-data directory relative to cargo manifest dir
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let test_data_path = Path::new(manifest_dir)
        .parent().unwrap()  // integration-tests
        .parent().unwrap()  // tests  
        .parent().unwrap()  // crates
        .join("test-data")
        .join("syntax");
    let mut results = TestResults::default();
    
    // Test each category
    test_category(&test_data_path.join("basic"), &mut results);
    test_category(&test_data_path.join("expressions"), &mut results);
    test_category(&test_data_path.join("types"), &mut results);
    test_category(&test_data_path.join("commands"), &mut results);
    test_category(&test_data_path.join("tactics"), &mut results);
    test_category(&test_data_path.join("patterns"), &mut results);
    test_category(&test_data_path.join("unicode"), &mut results);
    
    // Errors should fail to parse
    test_errors(&test_data_path.join("errors"), &mut results);
    
    results.print_summary();
    
    // Fail the test if success rate is too low
    assert!(
        results.success_rate() > 0.7,
        "Parser success rate too low: {:.1}%",
        results.success_rate() * 100.0
    );
}

fn test_category(dir: &Path, results: &mut TestResults) {
    let category = dir.file_name().unwrap().to_string_lossy();
    println!("\n=== Testing {} ===", category);
    
    let entries = fs::read_dir(dir).expect("Failed to read directory");
    
    for entry in entries {
        let entry = entry.expect("Failed to read entry");
        let path = entry.path();
        
        if path.extension().map_or(false, |ext| ext == "lean") {
            test_file(&path, results);
        }
    }
}

fn test_file(path: &Path, results: &mut TestResults) {
    let filename = path.file_name().unwrap().to_string_lossy();
    print!("  {} ... ", filename);
    
    let content = fs::read_to_string(path).expect("Failed to read file");
    let mut parser = Parser::new(&content);
    
    match parser.module() {
        Ok(_) => {
            println!("✅ OK");
            results.passed += 1;
        }
        Err(e) => {
            println!("❌ FAILED: {}", e);
            results.failed.push(FailedTest {
                file: path.to_path_buf(),
                error: e.to_string(),
            });
        }
    }
}

fn test_errors(dir: &Path, results: &mut TestResults) {
    println!("\n=== Testing error cases ===");
    
    let entries = fs::read_dir(dir).expect("Failed to read directory");
    
    for entry in entries {
        let entry = entry.expect("Failed to read entry");
        let path = entry.path();
        
        if path.extension().map_or(false, |ext| ext == "lean") {
            let filename = path.file_name().unwrap().to_string_lossy();
            print!("  {} ... ", filename);
            
            let content = fs::read_to_string(&path).expect("Failed to read file");
            let mut parser = Parser::new(&content);
            
            match parser.module() {
                Ok(_) => {
                    println!("❌ SHOULD HAVE FAILED");
                    results.should_have_failed += 1;
                }
                Err(_) => {
                    println!("✅ Failed as expected");
                    results.errors_caught += 1;
                }
            }
        }
    }
}

#[derive(Default)]
struct TestResults {
    passed: usize,
    failed: Vec<FailedTest>,
    errors_caught: usize,
    should_have_failed: usize,
}

struct FailedTest {
    file: PathBuf,
    error: String,
}

impl TestResults {
    fn total(&self) -> usize {
        self.passed + self.failed.len()
    }
    
    fn success_rate(&self) -> f64 {
        if self.total() == 0 {
            0.0
        } else {
            self.passed as f64 / self.total() as f64
        }
    }
    
    fn print_summary(&self) {
        println!("\n=== Test Summary ===");
        println!("Syntax tests: {} passed, {} failed ({:.1}% success rate)",
            self.passed, 
            self.failed.len(),
            self.success_rate() * 100.0
        );
        println!("Error tests: {} correctly caught, {} incorrectly passed",
            self.errors_caught,
            self.should_have_failed
        );
        
        if !self.failed.is_empty() {
            println!("\nFailed tests:");
            for (i, failed) in self.failed.iter().enumerate() {
                if i >= 10 {
                    println!("  ... and {} more", self.failed.len() - 10);
                    break;
                }
                println!("  {}: {}", 
                    failed.file.display(), 
                    failed.error
                );
            }
        }
    }
}