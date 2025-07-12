//! Core analysis infrastructure for the Lean analyzer
//!
//! This module provides the main analysis host that coordinates parsing,
//! elaboration, and type checking to provide IDE services.

use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use dashmap::DashMap;
use lean_elaborator::{ElabError, Elaborator};
use lean_kernel::{Environment, Expr, Name};
use lean_parser::{ParseError, Parser};
use parking_lot::RwLock;
use tracing::{debug, info, warn};

use crate::{
    error_reporting::ErrorReporter, file_system::FileSystem, project::Project,
    symbol_index::SymbolIndex,
};

/// The main analysis host that coordinates all analysis services
pub struct AnalysisHost {
    #[allow(dead_code)]
    file_system: Arc<FileSystem>,
    projects: RwLock<Vec<Project>>,
    file_analyses: DashMap<PathBuf, FileAnalysis>,
    symbol_index: Arc<RwLock<SymbolIndex>>,
    #[allow(dead_code)]
    error_reporter: ErrorReporter,
    environment: RwLock<Environment>,
}

/// Analysis results for a single file
#[derive(Debug, Clone)]
pub struct FileAnalysis {
    pub path: PathBuf,
    pub version: i32,
    pub parse_tree: Option<ParseTree>,
    pub elaborated_expr: Option<Expr>,
    pub parse_errors: Vec<ParseError>,
    pub elab_errors: Vec<String>, /* Store error messages as strings since ElabError doesn't
                                   * implement Clone */
    pub symbols: Vec<Symbol>,
    pub dependencies: Vec<PathBuf>,
}

/// Simplified parse tree representation
#[derive(Debug, Clone)]
pub struct ParseTree {
    pub root: SyntaxNode,
}

/// Syntax node in the parse tree
#[derive(Debug, Clone)]
pub struct SyntaxNode {
    pub kind: SyntaxKind,
    pub range: TextRange,
    pub children: Vec<SyntaxNode>,
    pub text: Option<String>,
}

/// Different kinds of syntax nodes
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxKind {
    Root,
    Definition,
    Theorem,
    Inductive,
    Structure,
    Instance,
    Expr,
    Type,
    Identifier,
    Literal,
    Comment,
    Error,
}

/// Text range for source locations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TextRange {
    pub start: usize,
    pub end: usize,
}

/// Symbol information for navigation and search
#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: Name,
    pub kind: SymbolKind,
    pub range: TextRange,
    pub definition_range: Option<TextRange>,
    pub signature: Option<String>,
    pub documentation: Option<String>,
}

/// Different kinds of symbols
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind {
    Definition,
    Theorem,
    Lemma,
    Axiom,
    Inductive,
    Constructor,
    Structure,
    Field,
    Instance,
    Variable,
    Namespace,
    Module,
}

impl AnalysisHost {
    pub fn new(file_system: Arc<FileSystem>) -> Self {
        Self {
            file_system,
            projects: RwLock::new(Vec::new()),
            file_analyses: DashMap::new(),
            symbol_index: Arc::new(RwLock::new(SymbolIndex::new())),
            error_reporter: ErrorReporter::new(),
            environment: RwLock::new(Environment::new()),
        }
    }

    /// Add a project to the analysis host
    pub fn add_project(&self, project: Project) {
        info!("Adding project: {}", project.root_path().display());
        self.projects.write().push(project);
    }

    /// Analyze a file and return the analysis results
    pub async fn analyze_file(
        &self,
        path: &Path,
        content: &str,
        version: i32,
    ) -> anyhow::Result<FileAnalysis> {
        debug!("Analyzing file: {}", path.display());

        let mut analysis = FileAnalysis {
            path: path.to_path_buf(),
            version,
            parse_tree: None,
            elaborated_expr: None,
            parse_errors: Vec::new(),
            elab_errors: Vec::new(),
            symbols: Vec::new(),
            dependencies: Vec::new(),
        };

        // Parse the file
        match self.parse_file(content).await {
            Ok((parse_tree, symbols)) => {
                analysis.parse_tree = Some(parse_tree);
                analysis.symbols = symbols;
            }
            Err(errors) => {
                analysis.parse_errors = errors;
                warn!(
                    "Parse errors in {}: {} errors",
                    path.display(),
                    analysis.parse_errors.len()
                );
            }
        }

        // Elaborate if parsing succeeded
        if analysis.parse_tree.is_some() && analysis.parse_errors.is_empty() {
            match self.elaborate_file(&analysis).await {
                Ok(expr) => {
                    analysis.elaborated_expr = Some(expr);
                }
                Err(errors) => {
                    analysis.elab_errors = errors.into_iter().map(|e| e.to_string()).collect();
                    warn!(
                        "Elaboration errors in {}: {} errors",
                        path.display(),
                        analysis.elab_errors.len()
                    );
                }
            }
        }

        // Update symbol index
        self.update_symbol_index(&analysis);

        // Cache the analysis
        self.file_analyses
            .insert(path.to_path_buf(), analysis.clone());

        Ok(analysis)
    }

    /// Get cached analysis for a file
    pub fn get_file_analysis(&self, path: &Path) -> Option<FileAnalysis> {
        self.file_analyses
            .get(path)
            .map(|entry| entry.value().clone())
    }

    /// Invalidate analysis for a file (when it changes)
    pub fn invalidate_file(&self, path: &Path) {
        debug!("Invalidating analysis for: {}", path.display());
        self.file_analyses.remove(path);

        // Also invalidate any files that depend on this one
        let dependent_files: Vec<PathBuf> = self
            .file_analyses
            .iter()
            .filter(|entry| entry.value().dependencies.contains(&path.to_path_buf()))
            .map(|entry| entry.key().clone())
            .collect();

        for dep_path in dependent_files {
            self.file_analyses.remove(&dep_path);
        }
    }

    /// Find symbol definition
    pub fn find_definition(
        &self,
        path: &Path,
        position: TextRange,
    ) -> Option<(PathBuf, TextRange)> {
        let analysis = self.get_file_analysis(path)?;

        // Find symbol at position
        let symbol = analysis
            .symbols
            .iter()
            .find(|s| s.range.contains(position.start))?;

        // If it has a definition range in the same file, return it
        if let Some(def_range) = symbol.definition_range {
            return Some((path.to_path_buf(), def_range));
        }

        // Otherwise, search in symbol index
        self.symbol_index.read().find_definition(&symbol.name)
    }

    /// Find all references to a symbol
    pub fn find_references(&self, path: &Path, position: TextRange) -> Vec<(PathBuf, TextRange)> {
        let analysis = match self.get_file_analysis(path) {
            Some(analysis) => analysis,
            None => return vec![],
        };

        let symbol = analysis
            .symbols
            .iter()
            .find(|s| s.range.contains(position.start));

        if let Some(symbol) = symbol {
            self.symbol_index.read().find_references(&symbol.name)
        } else {
            vec![]
        }
    }

    /// Get hover information for a position
    pub fn get_hover_info(&self, path: &Path, position: TextRange) -> Option<HoverInfo> {
        let analysis = self.get_file_analysis(path)?;

        let symbol = analysis
            .symbols
            .iter()
            .find(|s| s.range.contains(position.start))?;

        Some(HoverInfo {
            range: symbol.range,
            signature: symbol.signature.clone(),
            documentation: symbol.documentation.clone(),
            symbol_kind: symbol.kind.clone(),
        })
    }

    /// Get completions at a position
    pub fn get_completions(&self, path: &Path, position: TextRange) -> Vec<CompletionItem> {
        let analysis = match self.get_file_analysis(path) {
            Some(analysis) => analysis,
            None => return vec![],
        };

        // Get completions from current scope
        let mut completions = Vec::new();

        // Add symbols from current file
        for symbol in &analysis.symbols {
            if symbol.range.start < position.start {
                completions.push(CompletionItem {
                    label: self.name_to_string(&symbol.name),
                    kind: completion_kind_from_symbol(&symbol.kind),
                    detail: symbol.signature.clone(),
                    documentation: symbol.documentation.clone(),
                    insert_text: None,
                });
            }
        }

        // Add symbols from imports and environment
        let env = self.environment.read();
        completions.extend(self.get_environment_completions(&env));

        completions
    }

    // Private helper methods

    async fn parse_file(&self, content: &str) -> Result<(ParseTree, Vec<Symbol>), Vec<ParseError>> {
        let mut parser = Parser::new(content);

        match parser.module() {
            Ok(syntax_tree) => {
                let parse_tree = self.convert_to_parse_tree(syntax_tree);
                let symbols = self.extract_symbols(&parse_tree);
                Ok((parse_tree, symbols))
            }
            Err(error) => Err(vec![*error]),
        }
    }

    async fn elaborate_file(&self, _analysis: &FileAnalysis) -> Result<Expr, Vec<ElabError>> {
        let _env = self.environment.read().clone();
        let _elaborator = Elaborator::new();

        // Set up context with imports and environment
        // TODO: Implement elaboration of the parse tree

        // For now, return a placeholder
        Err(vec![])
    }

    fn convert_to_parse_tree(&self, _syntax_tree: lean_syn_expr::Syntax) -> ParseTree {
        // TODO: Convert from parser's syntax tree to our simplified representation
        ParseTree {
            root: SyntaxNode {
                kind: SyntaxKind::Root,
                range: TextRange { start: 0, end: 0 },
                children: vec![],
                text: None,
            },
        }
    }

    fn extract_symbols(&self, _parse_tree: &ParseTree) -> Vec<Symbol> {
        // TODO: Extract symbols from parse tree
        vec![]
    }

    fn update_symbol_index(&self, analysis: &FileAnalysis) {
        let mut index = self.symbol_index.write();
        index.update_file(&analysis.path, &analysis.symbols);
    }

    fn name_to_string(&self, name: &Name) -> String {
        // TODO: Implement proper name formatting
        format!("{name:?}")
    }

    fn get_environment_completions(&self, _env: &Environment) -> Vec<CompletionItem> {
        // TODO: Get completions from the environment
        vec![]
    }
}

impl TextRange {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn contains(&self, position: usize) -> bool {
        position >= self.start && position < self.end
    }

    pub fn len(&self) -> usize {
        self.end - self.start
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

/// Hover information for IDE
#[derive(Debug, Clone)]
pub struct HoverInfo {
    pub range: TextRange,
    pub signature: Option<String>,
    pub documentation: Option<String>,
    pub symbol_kind: SymbolKind,
}

/// Completion item for IDE
#[derive(Debug, Clone)]
pub struct CompletionItem {
    pub label: String,
    pub kind: CompletionKind,
    pub detail: Option<String>,
    pub documentation: Option<String>,
    pub insert_text: Option<String>,
}

/// Completion item kinds
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompletionKind {
    Function,
    Variable,
    Keyword,
    Type,
    Constructor,
    Field,
    Module,
    Snippet,
}

fn completion_kind_from_symbol(symbol_kind: &SymbolKind) -> CompletionKind {
    match symbol_kind {
        SymbolKind::Definition | SymbolKind::Theorem | SymbolKind::Lemma => {
            CompletionKind::Function
        }
        SymbolKind::Variable => CompletionKind::Variable,
        SymbolKind::Inductive | SymbolKind::Structure => CompletionKind::Type,
        SymbolKind::Constructor => CompletionKind::Constructor,
        SymbolKind::Field => CompletionKind::Field,
        SymbolKind::Module | SymbolKind::Namespace => CompletionKind::Module,
        _ => CompletionKind::Variable,
    }
}
