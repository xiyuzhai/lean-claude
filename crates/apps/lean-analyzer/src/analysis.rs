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

impl SyntaxNode {
    pub fn new(
        kind: SyntaxKind,
        range: TextRange,
        children: Vec<SyntaxNode>,
        text: Option<String>,
    ) -> Self {
        Self {
            kind,
            range,
            children,
            text,
        }
    }
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

    /// Prepare call hierarchy item at a position
    pub fn prepare_call_hierarchy(
        &self,
        path: &Path,
        position: TextRange,
    ) -> Option<CallHierarchyItem> {
        let analysis = self.get_file_analysis(path)?;

        let symbol = analysis
            .symbols
            .iter()
            .find(|s| s.range.contains(position.start))?;

        // Only create call hierarchy for callable symbols
        match symbol.kind {
            SymbolKind::Definition | SymbolKind::Theorem | SymbolKind::Lemma => {
                Some(CallHierarchyItem {
                    name: self.name_to_string(&symbol.name),
                    kind: symbol.kind.clone(),
                    uri: path.to_string_lossy().to_string(),
                    range: symbol.range,
                    selection_range: symbol.definition_range.unwrap_or(symbol.range),
                    detail: symbol.signature.clone(),
                })
            }
            _ => None,
        }
    }

    /// Get incoming calls for a call hierarchy item
    pub fn get_incoming_calls(&self, item: &CallHierarchyItem) -> Vec<CallHierarchyCall> {
        let mut calls = Vec::new();

        // Search all files for references to this symbol
        for entry in self.file_analyses.iter() {
            let analysis = entry.value();

            // Find references in this file's parse tree
            if let Some(parse_tree) = &analysis.parse_tree {
                let file_calls =
                    self.find_calls_in_tree(&parse_tree.root, &item.name, &analysis.path);
                calls.extend(file_calls);
            }
        }

        calls
    }

    /// Get outgoing calls for a call hierarchy item
    pub fn get_outgoing_calls(&self, item: &CallHierarchyItem) -> Vec<CallHierarchyCall> {
        let path = PathBuf::from(&item.uri);
        let analysis = match self.get_file_analysis(&path) {
            Some(analysis) => analysis,
            None => return vec![],
        };

        let calls = Vec::new();

        // Find the symbol definition
        let symbol = analysis.symbols.iter().find(|s| s.range == item.range);

        if let Some(_symbol) = symbol {
            // TODO: Parse the function body and find outgoing calls
            // For now, we'll return empty as this requires more sophisticated
            // analysis
        }

        calls
    }

    /// Get document symbols for a file
    pub fn get_document_symbols(&self, path: &Path) -> Vec<DocumentSymbolItem> {
        let analysis = match self.get_file_analysis(path) {
            Some(analysis) => analysis,
            None => return vec![],
        };

        let mut document_symbols = Vec::new();

        // Create a hierarchical structure from flat symbols
        for symbol in &analysis.symbols {
            document_symbols.push(DocumentSymbolItem {
                name: self.name_to_string(&symbol.name),
                detail: symbol.signature.clone(),
                kind: symbol.kind.clone(),
                range: symbol.range,
                selection_range: symbol.definition_range.unwrap_or(symbol.range),
                children: vec![], // TODO: Add child symbols (e.g., methods in a structure)
            });
        }

        // Sort by position in file
        document_symbols.sort_by_key(|s| s.range.start);

        document_symbols
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

    fn convert_to_parse_tree(&self, syntax_tree: lean_syn_expr::Syntax) -> ParseTree {
        ParseTree {
            root: self.convert_syntax_node(&syntax_tree, 0).0,
        }
    }

    fn convert_syntax_node(
        &self,
        syntax: &lean_syn_expr::Syntax,
        mut offset: usize,
    ) -> (SyntaxNode, usize) {
        use lean_syn_expr::Syntax;

        match syntax {
            Syntax::Node(node) => {
                let start_offset = offset;
                let kind = self.map_syntax_kind(&node.kind);
                let mut children = Vec::new();

                for child in &node.children {
                    let (child_node, new_offset) = self.convert_syntax_node(child, offset);
                    children.push(child_node);
                    offset = new_offset;
                }

                let syntax_node = SyntaxNode::new(
                    kind,
                    TextRange {
                        start: start_offset,
                        end: offset,
                    },
                    children,
                    None,
                );

                (syntax_node, offset)
            }
            Syntax::Atom(atom) => {
                let text = atom.value.to_string();
                let text_len = text.len();
                let syntax_node = SyntaxNode::new(
                    self.infer_atom_kind(&text),
                    TextRange {
                        start: offset,
                        end: offset + text_len,
                    },
                    vec![],
                    Some(text),
                );
                (syntax_node, offset + text_len)
            }
            Syntax::Missing => {
                let syntax_node = SyntaxNode::new(
                    SyntaxKind::Error,
                    TextRange {
                        start: offset,
                        end: offset,
                    },
                    vec![],
                    None,
                );
                (syntax_node, offset)
            }
        }
    }

    fn map_syntax_kind(&self, kind: &lean_syn_expr::SyntaxKind) -> SyntaxKind {
        use lean_syn_expr::SyntaxKind as ParserKind;

        match kind {
            ParserKind::Module => SyntaxKind::Root,
            ParserKind::Def => SyntaxKind::Definition,
            ParserKind::Theorem => SyntaxKind::Theorem,
            ParserKind::Inductive => SyntaxKind::Inductive,
            ParserKind::Structure => SyntaxKind::Structure,
            ParserKind::Instance => SyntaxKind::Instance,
            ParserKind::App | ParserKind::Lambda | ParserKind::Let | ParserKind::Match => {
                SyntaxKind::Expr
            }
            ParserKind::Identifier => SyntaxKind::Identifier,
            ParserKind::NumLit | ParserKind::StringLit | ParserKind::CharLit => SyntaxKind::Literal,
            ParserKind::Comment => SyntaxKind::Comment,
            _ => SyntaxKind::Expr,
        }
    }

    fn infer_atom_kind(&self, text: &str) -> SyntaxKind {
        if text
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '.')
        {
            if text
                .chars()
                .next()
                .is_some_and(|c| c.is_alphabetic() || c == '_')
            {
                SyntaxKind::Identifier
            } else {
                SyntaxKind::Literal
            }
        } else if text.chars().all(|c| c.is_numeric()) {
            SyntaxKind::Literal
        } else {
            SyntaxKind::Expr
        }
    }

    fn extract_symbols(&self, parse_tree: &ParseTree) -> Vec<Symbol> {
        let mut symbols = Vec::new();
        self.extract_symbols_from_node(&parse_tree.root, &mut symbols);
        symbols
    }

    fn extract_symbols_from_node(&self, node: &SyntaxNode, symbols: &mut Vec<Symbol>) {
        match node.kind {
            SyntaxKind::Definition
            | SyntaxKind::Theorem
            | SyntaxKind::Inductive
            | SyntaxKind::Structure
            | SyntaxKind::Instance => {
                if let Some(symbol) = self.extract_declaration_symbol(node) {
                    symbols.push(symbol);
                }
            }
            _ => {}
        }

        // Recursively process children
        for child in &node.children {
            self.extract_symbols_from_node(child, symbols);
        }
    }

    fn extract_declaration_symbol(&self, node: &SyntaxNode) -> Option<Symbol> {
        // Find the identifier child that represents the name
        let name_node = node
            .children
            .iter()
            .find(|child| child.kind == SyntaxKind::Identifier)?;

        let name_text = name_node.text.as_ref()?;
        let symbol_kind = match node.kind {
            SyntaxKind::Definition => SymbolKind::Definition,
            SyntaxKind::Theorem => SymbolKind::Theorem,
            SyntaxKind::Inductive => SymbolKind::Inductive,
            SyntaxKind::Structure => SymbolKind::Structure,
            SyntaxKind::Instance => SymbolKind::Instance,
            _ => return None,
        };

        // Create a simple name from the text
        let name = Name::from(name_text.as_str());

        Some(Symbol {
            name,
            kind: symbol_kind,
            range: name_node.range,
            definition_range: Some(node.range),
            signature: self.extract_signature(node),
            documentation: self.extract_documentation(node),
        })
    }

    fn extract_signature(&self, node: &SyntaxNode) -> Option<String> {
        // Create a simple signature by collecting identifier texts
        let mut signature_parts = Vec::new();

        match node.kind {
            SyntaxKind::Definition => signature_parts.push("def".to_string()),
            SyntaxKind::Theorem => signature_parts.push("theorem".to_string()),
            SyntaxKind::Inductive => signature_parts.push("inductive".to_string()),
            SyntaxKind::Structure => signature_parts.push("structure".to_string()),
            SyntaxKind::Instance => signature_parts.push("instance".to_string()),
            _ => return None,
        }

        // Add the name
        if let Some(name_node) = node
            .children
            .iter()
            .find(|child| child.kind == SyntaxKind::Identifier)
        {
            if let Some(name_text) = &name_node.text {
                signature_parts.push(name_text.clone());
            }
        }

        Some(signature_parts.join(" "))
    }

    fn extract_documentation(&self, _node: &SyntaxNode) -> Option<String> {
        // TODO: Extract doc comments from preceding comment nodes
        None
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

    fn find_calls_in_tree(
        &self,
        node: &SyntaxNode,
        target_name: &str,
        file_path: &Path,
    ) -> Vec<CallHierarchyCall> {
        let mut calls = Vec::new();

        // Check if this node is a function call to the target
        if matches!(node.kind, SyntaxKind::Identifier) {
            if let Some(ref text) = node.text {
                if text == target_name {
                    // This is a call to our target function
                    // Find the enclosing function/definition
                    if let Some(caller) = self.find_enclosing_function(node, file_path) {
                        calls.push(CallHierarchyCall {
                            from: caller,
                            from_ranges: vec![node.range],
                        });
                    }
                }
            }
        }

        // Recursively search children
        for child in &node.children {
            calls.extend(self.find_calls_in_tree(child, target_name, file_path));
        }

        calls
    }

    fn find_enclosing_function(
        &self,
        target_node: &SyntaxNode,
        file_path: &Path,
    ) -> Option<CallHierarchyItem> {
        // Get the file analysis to access the parse tree
        let analysis = self.get_file_analysis(file_path)?;
        let parse_tree = analysis.parse_tree.as_ref()?;

        // Find the enclosing function by searching for parent nodes
        self.find_enclosing_function_recursive(&parse_tree.root, target_node, file_path)
    }

    fn find_enclosing_function_recursive(
        &self,
        current_node: &SyntaxNode,
        target_node: &SyntaxNode,
        file_path: &Path,
    ) -> Option<CallHierarchyItem> {
        // Check if target is within current node's range
        if !self.range_contains(&current_node.range, &target_node.range) {
            return None;
        }

        // If current node is a function definition and contains target, it's the
        // enclosing function
        if matches!(
            current_node.kind,
            SyntaxKind::Definition | SyntaxKind::Theorem | SyntaxKind::Instance
        ) {
            // Find the name of this function
            let name = current_node
                .children
                .iter()
                .find(|child| child.kind == SyntaxKind::Identifier)
                .and_then(|child| child.text.as_ref())
                .map(|s| s.to_string())
                .unwrap_or_else(|| "anonymous".to_string());

            return Some(CallHierarchyItem {
                name,
                kind: match current_node.kind {
                    SyntaxKind::Definition => SymbolKind::Definition,
                    SyntaxKind::Theorem => SymbolKind::Theorem,
                    SyntaxKind::Instance => SymbolKind::Instance,
                    _ => SymbolKind::Definition,
                },
                uri: file_path.to_string_lossy().to_string(),
                range: current_node.range,
                selection_range: current_node
                    .children
                    .iter()
                    .find(|child| child.kind == SyntaxKind::Identifier)
                    .map(|child| child.range)
                    .unwrap_or(current_node.range),
                detail: self.extract_signature(current_node),
            });
        }

        // Recursively search children for enclosing function
        for child in &current_node.children {
            if let Some(result) =
                self.find_enclosing_function_recursive(child, target_node, file_path)
            {
                return Some(result);
            }
        }

        None
    }

    fn range_contains(&self, outer: &TextRange, inner: &TextRange) -> bool {
        outer.start <= inner.start && inner.end <= outer.end
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

/// Call hierarchy item for IDE
#[derive(Debug, Clone)]
pub struct CallHierarchyItem {
    pub name: String,
    pub kind: SymbolKind,
    pub uri: String,
    pub range: TextRange,
    pub selection_range: TextRange,
    pub detail: Option<String>,
}

/// Call hierarchy call for IDE (incoming or outgoing)
#[derive(Debug, Clone)]
pub struct CallHierarchyCall {
    pub from: CallHierarchyItem,
    pub from_ranges: Vec<TextRange>,
}

/// Document symbol for IDE
#[derive(Debug, Clone)]
pub struct DocumentSymbolItem {
    pub name: String,
    pub detail: Option<String>,
    pub kind: SymbolKind,
    pub range: TextRange,
    pub selection_range: TextRange,
    pub children: Vec<DocumentSymbolItem>,
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
