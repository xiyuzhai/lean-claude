use std::sync::Arc;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use lean_analyzer::formatting::LeanFormatter;
use lsp_types::Url;
use tempfile::TempDir;

fn benchmark_parsing(c: &mut Criterion) {
    let content = r#"
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial]; exact Nat.mul_pos (Nat.succ_pos n) ih
"#;

    c.bench_function("parse_small_file", |b| {
        b.iter(|| {
            let mut parser = lean_parser::Parser::new(black_box(content));
            let _ = parser.module();
        });
    });
}

fn benchmark_formatting(c: &mut Criterion) {
    let content = "def    test   (  x   :   Nat  )  :   Nat   :=   x  +   1";
    let formatter = LeanFormatter::new();

    c.bench_function("format_simple", |b| {
        b.iter(|| {
            let _ = formatter.format_document(black_box(content));
        });
    });
}

fn benchmark_analysis(c: &mut Criterion) {
    let temp_dir = TempDir::new().unwrap();
    let root_uri = Url::from_file_path(temp_dir.path()).unwrap();
    let workspace = Arc::new(lean_analyzer::workspace::Workspace::new(Some(&root_uri)).unwrap());
    let analysis_host = lean_analyzer::analysis::AnalysisHost::new(workspace.file_system());

    let content = "def test : Nat := 42";
    let file_path = temp_dir.path().join("test.lean");
    std::fs::write(&file_path, content).unwrap();

    c.bench_function("analyze_file", |b| {
        b.iter(|| {
            let _ = futures::executor::block_on(analysis_host.analyze_file(
                &file_path,
                black_box(content),
                1,
            ));
        });
    });
}

fn benchmark_large_file(c: &mut Criterion) {
    // Generate a large file with many definitions
    let mut large_content = String::new();
    for i in 0..1000 {
        large_content.push_str(&format!("def function_{i} : Nat := {i}\n"));
    }

    c.bench_function("parse_large_file", |b| {
        b.iter(|| {
            let mut parser = lean_parser::Parser::new(black_box(&large_content));
            let _ = parser.module();
        });
    });
}

criterion_group!(
    benches,
    benchmark_parsing,
    benchmark_formatting,
    benchmark_analysis,
    benchmark_large_file
);
criterion_main!(benches);
