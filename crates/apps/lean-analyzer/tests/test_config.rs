//! Test configuration and utilities for lean-analyzer tests

use std::{path::PathBuf, sync::Arc};

use lean_analyzer::{analysis::AnalysisHost, workspace::Workspace};
use tempfile::TempDir;

/// Common test configuration
#[derive(Debug, Clone)]
pub struct TestConfig {
    pub enable_exhaustive_tests: bool,
    pub enable_performance_tests: bool,
    pub enable_real_world_tests: bool,
    pub max_test_time_ms: u64,
    pub large_file_threshold: usize,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            enable_exhaustive_tests: true,
            enable_performance_tests: true,
            enable_real_world_tests: true,
            max_test_time_ms: 5000,
            large_file_threshold: 1000,
        }
    }
}

/// Test workspace builder for consistent test setup
pub struct TestWorkspaceBuilder {
    #[allow(dead_code)]
    temp_dir: Option<TempDir>,
    files: Vec<(String, String)>,
    config: TestConfig,
}

impl Default for TestWorkspaceBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl TestWorkspaceBuilder {
    pub fn new() -> Self {
        Self {
            temp_dir: None,
            files: Vec::new(),
            config: TestConfig::default(),
        }
    }

    pub fn with_config(mut self, config: TestConfig) -> Self {
        self.config = config;
        self
    }

    pub fn add_file(mut self, name: &str, content: &str) -> Self {
        self.files.push((name.to_string(), content.to_string()));
        self
    }

    pub fn add_lean_file(self, name: &str, content: &str) -> Self {
        let filename = if name.ends_with(".lean") {
            name.to_string()
        } else {
            format!("{name}.lean")
        };
        self.add_file(&filename, content)
    }

    pub fn build(self) -> TestWorkspace {
        let temp_dir = TempDir::new().unwrap();

        // Create files
        for (name, content) in &self.files {
            let file_path = temp_dir.path().join(name);
            if let Some(parent) = file_path.parent() {
                std::fs::create_dir_all(parent).unwrap();
            }
            std::fs::write(&file_path, content).unwrap();
        }

        // Create workspace
        let _workspace_path = temp_dir.path().to_path_buf();
        let workspace = Arc::new(Workspace::new(None).unwrap());
        let analysis_host = AnalysisHost::new(workspace.file_system());

        TestWorkspace {
            temp_dir,
            workspace,
            analysis_host,
            files: self.files,
            config: self.config,
        }
    }
}

/// Test workspace with analysis capabilities
pub struct TestWorkspace {
    pub temp_dir: TempDir,
    pub workspace: Arc<Workspace>,
    pub analysis_host: AnalysisHost,
    pub files: Vec<(String, String)>,
    pub config: TestConfig,
}

impl TestWorkspace {
    pub fn file_path(&self, name: &str) -> PathBuf {
        self.temp_dir.path().join(name)
    }

    pub fn file_content(&self, name: &str) -> Option<&str> {
        self.files
            .iter()
            .find(|(filename, _)| filename == name)
            .map(|(_, content)| content.as_str())
    }

    pub async fn analyze_file(
        &self,
        name: &str,
    ) -> anyhow::Result<lean_analyzer::analysis::FileAnalysis> {
        let path = self.file_path(name);
        let content = self
            .file_content(name)
            .ok_or_else(|| anyhow::anyhow!("File not found: {}", name))?;

        self.analysis_host.analyze_file(&path, content, 1).await
    }

    pub fn list_files(&self) -> Vec<&str> {
        self.files.iter().map(|(name, _)| name.as_str()).collect()
    }
}

/// Common test data for various scenarios
pub struct TestData;

impl TestData {
    /// Basic Lean function definitions
    pub fn basic_functions() -> &'static str {
        r#"
-- Basic function definitions
def identity (x : α) : α := x

def add (x y : Nat) : Nat := x + y

def multiply (x y : Nat) : Nat := x * y

def greeting (name : String) : String := "Hello, " ++ name
"#
    }

    /// Code with common beginner errors
    pub fn beginner_errors() -> &'static str {
        r#"
-- Common beginner mistakes

-- Missing parentheses
def broken1 x := x + 1

-- Missing type annotation  
def broken2 (x Nat) := x

-- Wrong syntax
function broken3(x) { return x + 1; }

-- Typo in type name
def broken4 : Strng := "hello"

-- Missing import
def broken5 : List Nat := [1, 2, 3]
"#
    }

    /// Import and namespace examples
    pub fn import_examples() -> &'static str {
        r#"
import Std.Data.List.Basic
import Std.Data.Array.Basic

-- Using imported functions
def list_example := List.map (+1) [1, 2, 3]

def array_example := Array.map (*2) #[1, 2, 3]

-- Namespace conflicts
open List
open Array

def ambiguous := map (+1) [1, 2, 3]  -- Which map?
"#
    }

    /// Complex type definitions
    pub fn complex_types() -> &'static str {
        r#"
-- Inductive types
inductive Color
| red
| green  
| blue

-- Structures
structure Point where
  x : Float
  y : Float

-- Type classes
class Additive (α : Type) where
  add : α → α → α
  zero : α

-- Instances
instance : Additive Nat where
  add := Nat.add
  zero := 0
"#
    }

    /// Theorems and proofs
    pub fn theorem_examples() -> &'static str {
        r#"
-- Basic theorems
theorem add_comm (x y : Nat) : x + y = y + x := by
  induction x with
  | zero => simp
  | succ n ih => simp [Nat.add_succ, ih]

-- Lemmas
lemma zero_add (n : Nat) : 0 + n = n := by simp

-- Invalid proofs (for error testing)
theorem broken_proof (x : Nat) : x = x + 1 := by
  sorry  -- This should be flagged
"#
    }

    /// Large file content for performance testing
    pub fn large_file_content(num_functions: usize) -> String {
        let mut content = String::new();

        content.push_str("-- Auto-generated large file for performance testing\n\n");
        content.push_str("import Std.Data.List.Basic\nimport Std.Data.Array.Basic\n\n");

        for i in 0..num_functions {
            content.push_str(&format!("def function_{i} (x : Nat) : Nat := x + {i}\n\n"));

            if i.is_multiple_of(5) {
                content.push_str(&format!(
                    "def list_function_{} : List Nat := List.replicate {} {}\n\n",
                    i,
                    i + 1,
                    i
                ));
            }

            if i.is_multiple_of(10) {
                content.push_str(&format!(
                    "theorem theorem_{i} : function_{i} 0 = {i} := by simp [function_{i}]\n\n"
                ));
            }
        }

        content
    }

    /// Real-world Lean code patterns
    pub fn real_world_patterns() -> &'static str {
        r#"
-- Real-world patterns commonly seen in Lean projects

-- Option and Result handling
def safe_division (x y : Nat) : Option Nat :=
  if y = 0 then none else some (x / y)

def handle_result (x : Result String Nat) : String :=
  match x with
  | Result.ok n => s!"Success: {n}"
  | Result.error msg => s!"Error: {msg}"

-- Monad usage
def compute_result : IO (Result String Nat) := do
  let input ← IO.getStdin
  let line ← input.getLine
  match line.trim.toNat? with
  | some n => pure (Result.ok n)
  | none => pure (Result.error "Invalid number")

-- Advanced pattern matching
def complex_match (x : Nat × Option String) : String :=
  match x with
  | (0, none) => "zero and nothing"
  | (0, some s) => s!"zero and {s}"
  | (n, none) => s!"number {n} and nothing"
  | (n, some s) => s!"number {n} and {s}"

-- Dependent types
def vector_head {α : Type} {n : Nat} (v : Vector α (n + 1)) : α :=
  v.head

-- Tactic usage
theorem vector_cons_head {α : Type} (x : α) (xs : Vector α n) :
  vector_head (Vector.cons x xs) = x := by
  simp [vector_head, Vector.head]
"#
    }
}

/// Test assertion helpers
pub struct TestAssertions;

impl TestAssertions {
    /// Assert that error message quality meets our standards
    pub fn assert_good_error_message(message: &str, explanation: Option<&str>) {
        // Error message should be clear and specific
        assert!(!message.is_empty(), "Error message should not be empty");
        assert!(message.len() > 10, "Error message should be descriptive");
        assert!(
            !message.contains("internal error"),
            "Should not expose internal errors"
        );

        // Should have helpful explanation for beginners
        if let Some(exp) = explanation {
            assert!(!exp.is_empty(), "Explanation should not be empty");
            assert!(exp.len() > 20, "Explanation should be detailed");
            assert!(
                exp.contains("you") || exp.contains("try") || exp.contains("make sure"),
                "Explanation should be user-friendly"
            );
        }
    }

    /// Assert that suggestions are helpful and actionable
    pub fn assert_good_suggestions(suggestions: &[lean_analyzer::error_reporting::CodeSuggestion]) {
        for suggestion in suggestions {
            assert!(
                !suggestion.description.is_empty(),
                "Suggestion description should not be empty"
            );
            assert!(
                !suggestion.replacement.is_empty(),
                "Suggestion replacement should not be empty"
            );
            assert!(
                suggestion.description.len() > 5,
                "Suggestion description should be descriptive"
            );
        }
    }

    /// Assert that response times are acceptable
    pub fn assert_performance(duration_ms: u64, operation: &str, max_ms: u64) {
        assert!(
            duration_ms <= max_ms,
            "{operation} took {duration_ms}ms, should be under {max_ms}ms"
        );
    }

    /// Assert that diagnostic count is reasonable
    pub fn assert_diagnostic_quality(
        parse_errors: usize,
        elab_errors: usize,
        content_lines: usize,
    ) {
        // Should not have excessive errors for reasonable code
        let total_errors = parse_errors + elab_errors;
        let error_rate = total_errors as f64 / content_lines as f64;

        assert!(
            error_rate < 0.5,
            "Error rate too high: {} errors for {} lines ({}% error rate)",
            total_errors,
            content_lines,
            error_rate * 100.0
        );
    }
}

/// Test categories for organized test execution
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestCategory {
    Unit,
    Integration,
    Performance,
    RealWorld,
    Regression,
}

/// Test marker trait for categorizing tests
pub trait TestMarker {
    fn category() -> TestCategory;
    fn timeout_ms() -> u64;
    fn skip_in_ci() -> bool {
        false
    }
}

/// Marker for unit tests
pub struct UnitTest;
impl TestMarker for UnitTest {
    fn category() -> TestCategory {
        TestCategory::Unit
    }
    fn timeout_ms() -> u64 {
        1000
    }
}

/// Marker for integration tests  
pub struct IntegrationTest;
impl TestMarker for IntegrationTest {
    fn category() -> TestCategory {
        TestCategory::Integration
    }
    fn timeout_ms() -> u64 {
        5000
    }
}

/// Marker for performance tests
pub struct PerformanceTest;
impl TestMarker for PerformanceTest {
    fn category() -> TestCategory {
        TestCategory::Performance
    }
    fn timeout_ms() -> u64 {
        10000
    }
    fn skip_in_ci() -> bool {
        std::env::var("CI").is_ok() && std::env::var("RUN_PERF_TESTS").is_err()
    }
}

/// Marker for real-world scenario tests
pub struct RealWorldTest;
impl TestMarker for RealWorldTest {
    fn category() -> TestCategory {
        TestCategory::RealWorld
    }
    fn timeout_ms() -> u64 {
        15000
    }
    fn skip_in_ci() -> bool {
        std::env::var("CI").is_ok() && std::env::var("RUN_REAL_WORLD_TESTS").is_err()
    }
}
