//! Performance benchmarks for lean-analyzer
//!
//! These benchmarks ensure the analyzer performs well on real-world scenarios
//! and maintains sub-100ms response times for common operations.

use std::{path::PathBuf, sync::Arc, time::Duration};

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use lean_analyzer::{
    analysis::{AnalysisHost, TextRange},
    code_actions::CodeActionProvider,
    error_reporting::ErrorReporter,
    file_system::FileSystem,
    formatting::LeanFormatter,
    workspace::Workspace,
};
use lsp_types::{
    CodeActionContext, CodeActionParams, Diagnostic, DiagnosticSeverity, Range,
    TextDocumentIdentifier, Url,
};
use tempfile::TempDir;
use tokio::runtime::Runtime;

/// Benchmark fixture for consistent test setup
struct BenchmarkFixture {
    temp_dir: TempDir,
    runtime: Runtime,
    analysis_host: AnalysisHost,
    error_reporter: ErrorReporter,
    code_actions: CodeActionProvider,
    formatter: LeanFormatter,
}

impl BenchmarkFixture {
    fn new() -> Self {
        let temp_dir = TempDir::new().unwrap();
        let runtime = Runtime::new().unwrap();
        let workspace_path = temp_dir.path().to_path_buf();
        let file_system = Arc::new(FileSystem::new());
        let workspace = Arc::new(Workspace::new(workspace_path, file_system.clone()));
        let analysis_host = AnalysisHost::new(file_system);
        let error_reporter = ErrorReporter::new();
        let code_actions = CodeActionProvider::new();
        let formatter = LeanFormatter::new();

        Self {
            temp_dir,
            runtime,
            analysis_host,
            error_reporter,
            code_actions,
            formatter,
        }
    }

    fn create_test_file(&self, name: &str, content: &str) -> PathBuf {
        let path = self.temp_dir.path().join(name);
        std::fs::write(&path, content).unwrap();
        path
    }
}

/// Generate Lean code of various sizes for benchmarking
fn generate_lean_code(num_functions: usize) -> String {
    let mut code = String::new();

    // Add some imports
    code.push_str("import Std.Data.List.Basic\n");
    code.push_str("import Std.Data.Array.Basic\n\n");

    // Add function definitions
    for i in 0..num_functions {
        code.push_str(&format!(
            "def function_{} (x : Nat) : Nat := x + {}\n\n",
            i, i
        ));

        // Add some with errors occasionally
        if i % 10 == 0 {
            code.push_str(&format!(
                "def broken_{} x := x + {}  -- Missing type annotation\n\n",
                i, i
            ));
        }

        // Add some complex expressions
        if i % 5 == 0 {
            code.push_str(&format!(
                "def complex_{} : List Nat := List.map (+{}) [1, 2, 3, 4, 5]\n\n",
                i, i
            ));
        }
    }

    code
}

/// Benchmark parsing performance
fn bench_parsing(c: &mut Criterion) {
    let fixture = BenchmarkFixture::new();

    let mut group = c.benchmark_group("parsing");

    for size in [10, 50, 100, 500, 1000].iter() {
        let code = generate_lean_code(*size);
        let file_path = fixture.create_test_file(&format!("bench_{}.lean", size), &code);

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::new("analyze_file", size), size, |b, _| {
            b.to_async(&fixture.runtime).iter(|| async {
                black_box(
                    fixture
                        .analysis_host
                        .analyze_file(&file_path, &code, 1)
                        .await,
                )
            });
        });
    }

    group.finish();
}

/// Benchmark error reporting performance
fn bench_error_reporting(c: &mut Criterion) {
    let fixture = BenchmarkFixture::new();

    let mut group = c.benchmark_group("error_reporting");

    // Test common error types
    let error_scenarios = vec![
        (
            "missing_parentheses",
            "def f x := x + 1",
            lean_parser::ParseErrorKind::Expected("(".to_string()),
        ),
        (
            "missing_colon",
            "def f (x Nat) := x",
            lean_parser::ParseErrorKind::Expected(":".to_string()),
        ),
        (
            "unexpected_char",
            "def f := x @ y",
            lean_parser::ParseErrorKind::UnexpectedChar('@'),
        ),
        (
            "unknown_identifier",
            "def f := unknown_var",
            lean_parser::ParseErrorKind::Custom("Unknown identifier 'unknown_var'".to_string()),
        ),
    ];

    for (name, source, error_kind) in error_scenarios {
        let error = lean_parser::ParseError {
            kind: error_kind,
            position: lean_parser::Position { line: 0, column: 0 },
            range: None,
        };

        group.bench_function(name, |b| {
            b.iter(|| black_box(fixture.error_reporter.enhance_parse_error(&error, source)));
        });
    }

    group.finish();
}

/// Benchmark code actions performance
fn bench_code_actions(c: &mut Criterion) {
    let fixture = BenchmarkFixture::new();

    let mut group = c.benchmark_group("code_actions");

    let test_scenarios = vec![
        (
            "import_suggestion",
            "def f : Nat := 5",
            "Unknown identifier 'Nat'",
            0,
            8,
            0,
            11,
        ),
        ("syntax_fix", "def f x := x + 1", "Expected '('", 0, 6, 0, 7),
        (
            "type_annotation",
            "def f x := x + 1",
            "Cannot infer type",
            0,
            6,
            0,
            7,
        ),
    ];

    for (name, source, error_msg, start_line, start_char, end_line, end_char) in test_scenarios {
        let uri = Url::parse("file:///test.lean").unwrap();
        let diagnostic = Diagnostic {
            range: Range {
                start: lsp_types::Position::new(start_line, start_char),
                end: lsp_types::Position::new(end_line, end_char),
            },
            severity: Some(DiagnosticSeverity::ERROR),
            code: None,
            code_description: None,
            source: Some("lean-analyzer".to_string()),
            message: error_msg.to_string(),
            related_information: None,
            tags: None,
            data: None,
        };

        let params = CodeActionParams {
            text_document: TextDocumentIdentifier { uri },
            range: diagnostic.range,
            context: CodeActionContext {
                diagnostics: vec![diagnostic],
                only: None,
                trigger_kind: None,
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        group.bench_function(name, |b| {
            b.iter(|| black_box(fixture.code_actions.get_code_actions(&params, source)));
        });
    }

    group.finish();
}

/// Benchmark formatting performance
fn bench_formatting(c: &mut Criterion) {
    let fixture = BenchmarkFixture::new();

    let mut group = c.benchmark_group("formatting");

    // Test different code sizes and complexity
    for size in [10, 50, 100, 500, 1000].iter() {
        let code = generate_lean_code(*size);

        group.throughput(Throughput::Bytes(code.len() as u64));
        group.bench_with_input(
            BenchmarkId::new("format_document", size),
            &code,
            |b, code| {
                b.iter(|| black_box(fixture.formatter.format_document(code)));
            },
        );
    }

    // Test specific formatting scenarios
    let formatting_scenarios = vec![
        ("simple_function", "def   test(x:Nat):Nat:=x+1"),
        ("complex_match", "def f := match x with\n|0=>1\n|n+1=>n"),
        (
            "nested_expressions",
            "def complex := (((x + y) * z) / w) + ((a - b) * (c + d))",
        ),
        (
            "long_parameter_list",
            "def f (a : Nat) (b : String) (c : List Nat) (d : Array String) : Nat := a + b.length",
        ),
    ];

    for (name, code) in formatting_scenarios {
        group.bench_function(name, |b| {
            b.iter(|| black_box(fixture.formatter.format_document(code)));
        });
    }

    group.finish();
}

/// Benchmark hover and completion performance
fn bench_ide_features(c: &mut Criterion) {
    let fixture = BenchmarkFixture::new();

    let mut group = c.benchmark_group("ide_features");

    let code =
        "def helper : Nat := 42\ndef main := helper + 1\ndef test := List.map (+1) [1, 2, 3]";
    let file_path = fixture.create_test_file("ide_test.lean", code);

    // Benchmark hover info
    group.bench_function("hover_info", |b| {
        b.to_async(&fixture.runtime).iter(|| async {
            let _ = fixture
                .analysis_host
                .analyze_file(&file_path, code, 1)
                .await;
            black_box(
                fixture
                    .analysis_host
                    .get_hover_info(&file_path, TextRange::new(30, 36)),
            )
        });
    });

    // Benchmark completion
    group.bench_function("completions", |b| {
        b.to_async(&fixture.runtime).iter(|| async {
            let _ = fixture
                .analysis_host
                .analyze_file(&file_path, code, 1)
                .await;
            black_box(
                fixture
                    .analysis_host
                    .get_completions(&file_path, TextRange::new(50, 50)),
            )
        });
    });

    // Benchmark goto definition
    group.bench_function("goto_definition", |b| {
        b.to_async(&fixture.runtime).iter(|| async {
            let _ = fixture
                .analysis_host
                .analyze_file(&file_path, code, 1)
                .await;
            black_box(
                fixture
                    .analysis_host
                    .find_definition(&file_path, TextRange::new(30, 36)),
            )
        });
    });

    // Benchmark find references
    group.bench_function("find_references", |b| {
        b.to_async(&fixture.runtime).iter(|| async {
            let _ = fixture
                .analysis_host
                .analyze_file(&file_path, code, 1)
                .await;
            black_box(
                fixture
                    .analysis_host
                    .find_references(&file_path, TextRange::new(4, 10)),
            )
        });
    });

    group.finish();
}

/// Benchmark memory usage and caching
fn bench_memory_performance(c: &mut Criterion) {
    let fixture = BenchmarkFixture::new();

    let mut group = c.benchmark_group("memory");

    // Test repeated analysis of the same file (should use caching)
    let code = generate_lean_code(100);
    let file_path = fixture.create_test_file("cache_test.lean", &code);

    group.bench_function("repeated_analysis", |b| {
        b.to_async(&fixture.runtime).iter(|| async {
            // First analysis
            let _ = fixture
                .analysis_host
                .analyze_file(&file_path, &code, 1)
                .await;
            // Second analysis (should be faster due to caching)
            black_box(
                fixture
                    .analysis_host
                    .analyze_file(&file_path, &code, 1)
                    .await,
            )
        });
    });

    // Test file invalidation and re-analysis
    group.bench_function("invalidation_and_reanalysis", |b| {
        b.to_async(&fixture.runtime).iter(|| async {
            let _ = fixture
                .analysis_host
                .analyze_file(&file_path, &code, 1)
                .await;
            fixture.analysis_host.invalidate_file(&file_path);
            black_box(
                fixture
                    .analysis_host
                    .analyze_file(&file_path, &code, 2)
                    .await,
            )
        });
    });

    group.finish();
}

/// Benchmark realistic workflow scenarios
fn bench_real_world_scenarios(c: &mut Criterion) {
    let fixture = BenchmarkFixture::new();

    let mut group = c.benchmark_group("real_world");

    // Simulate a typical editing session
    let edit_stages = vec![
        "def f",
        "def f (",
        "def f (x",
        "def f (x :",
        "def f (x : Nat",
        "def f (x : Nat)",
        "def f (x : Nat) :",
        "def f (x : Nat) : Nat",
        "def f (x : Nat) : Nat :=",
        "def f (x : Nat) : Nat := x + 1",
    ];

    group.bench_function("incremental_editing", |b| {
        b.to_async(&fixture.runtime).iter(|| async {
            let file_path = fixture.temp_dir.path().join("incremental.lean");

            for (version, content) in edit_stages.iter().enumerate() {
                black_box(
                    fixture
                        .analysis_host
                        .analyze_file(&file_path, content, version as i32 + 1)
                        .await,
                );
            }
        });
    });

    // Simulate working with imports and multiple files
    let files = vec![
        ("base.lean", "def shared : Nat := 42"),
        ("user.lean", "import Base\ndef use_shared := shared + 1"),
        (
            "complex.lean",
            "import Base\nimport User\ndef complex := use_shared * shared",
        ),
    ];

    group.bench_function("multi_file_analysis", |b| {
        b.to_async(&fixture.runtime).iter(|| async {
            for (filename, content) in &files {
                let file_path = fixture.temp_dir.path().join(filename);
                black_box(
                    fixture
                        .analysis_host
                        .analyze_file(&file_path, content, 1)
                        .await,
                );
            }
        });
    });

    group.finish();
}

/// Benchmark response time requirements (should be under 100ms)
fn bench_response_times(c: &mut Criterion) {
    let fixture = BenchmarkFixture::new();

    let mut group = c.benchmark_group("response_times");
    group.measurement_time(Duration::from_secs(10));
    group.sample_size(100);

    // Set strict timing requirements
    let small_code = generate_lean_code(10);
    let medium_code = generate_lean_code(50);

    let small_file = fixture.create_test_file("small.lean", &small_code);
    let medium_file = fixture.create_test_file("medium.lean", &medium_code);

    // These should complete in under 100ms
    group.bench_function("small_file_analysis_100ms", |b| {
        b.to_async(&fixture.runtime).iter(|| async {
            black_box(
                fixture
                    .analysis_host
                    .analyze_file(&small_file, &small_code, 1)
                    .await,
            )
        });
    });

    group.bench_function("formatting_100ms", |b| {
        b.iter(|| black_box(fixture.formatter.format_document(&medium_code)));
    });

    group.bench_function("error_reporting_100ms", |b| {
        let error = lean_parser::ParseError {
            kind: lean_parser::ParseErrorKind::Expected("(".to_string()),
            position: lean_parser::Position { line: 0, column: 0 },
            range: None,
        };

        b.iter(|| {
            black_box(
                fixture
                    .error_reporter
                    .enhance_parse_error(&error, "def f x := x + 1"),
            )
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_parsing,
    bench_error_reporting,
    bench_code_actions,
    bench_formatting,
    bench_ide_features,
    bench_memory_performance,
    bench_real_world_scenarios,
    bench_response_times
);
criterion_main!(benches);
