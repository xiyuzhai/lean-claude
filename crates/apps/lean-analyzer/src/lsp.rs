//! LSP server implementation for lean-analyzer

use std::{collections::HashMap, sync::Arc};

use lsp_server::{Connection, Message};
use lsp_types::*;
use serde_json::Value;
use tokio::sync::RwLock;
use tracing::{debug, error, info, warn};

use crate::{
    analysis::{AnalysisHost, CompletionItem, HoverInfo, TextRange},
    code_actions::CodeActionProvider,
    error_reporting::ErrorReporter,
    formatting::LeanFormatter,
    inlay_hints::{InlayHintConfig, InlayHintProvider},
    semantic_highlighting::SemanticHighlighter,
    workspace::Workspace,
};

pub struct LeanLanguageServer {
    #[allow(dead_code)]
    workspace: Arc<Workspace>,
    analysis_host: Arc<AnalysisHost>,
    error_reporter: ErrorReporter,
    code_actions: CodeActionProvider,
    formatter: LeanFormatter,
    semantic_highlighter: Arc<RwLock<SemanticHighlighter>>,
    inlay_hint_provider: Arc<RwLock<InlayHintProvider>>,
    #[allow(dead_code)]
    client_capabilities: RwLock<Option<ClientCapabilities>>,
    file_versions: RwLock<HashMap<Url, i32>>,
}

impl LeanLanguageServer {
    pub fn new(workspace: Arc<Workspace>) -> Self {
        let analysis_host = Arc::new(AnalysisHost::new(workspace.file_system()));

        Self {
            workspace,
            analysis_host,
            error_reporter: ErrorReporter::new(),
            code_actions: CodeActionProvider::new(),
            formatter: LeanFormatter::new(),
            semantic_highlighter: Arc::new(RwLock::new(SemanticHighlighter::new())),
            inlay_hint_provider: Arc::new(RwLock::new(InlayHintProvider::new(
                InlayHintConfig::default(),
            ))),
            client_capabilities: RwLock::new(None),
            file_versions: RwLock::new(HashMap::new()),
        }
    }

    pub async fn run(self, connection: Connection) -> anyhow::Result<()> {
        info!("LSP server main loop starting");

        for msg in &connection.receiver {
            match msg {
                Message::Request(req) => {
                    if connection.handle_shutdown(&req)? {
                        info!("Received shutdown request");
                        break;
                    }

                    self.handle_request(&connection, req).await;
                }
                Message::Notification(not) => {
                    self.handle_notification(&connection, not).await;
                }
                Message::Response(resp) => {
                    warn!("Received unexpected response: {:?}", resp);
                }
            }
        }

        info!("LSP server main loop finished");
        Ok(())
    }

    async fn handle_request(&self, connection: &Connection, req: lsp_server::Request) {
        debug!("Handling request: {}", req.method);

        let result = match req.method.as_str() {
            "textDocument/hover" => {
                let params: HoverParams = serde_json::from_value(req.params).unwrap();
                self.handle_hover(params).await
            }
            "textDocument/completion" => {
                let params: CompletionParams = serde_json::from_value(req.params).unwrap();
                self.handle_completion(params).await
            }
            "textDocument/definition" => {
                let params: GotoDefinitionParams = serde_json::from_value(req.params).unwrap();
                self.handle_goto_definition(params).await
            }
            "textDocument/references" => {
                let params: ReferenceParams = serde_json::from_value(req.params).unwrap();
                self.handle_find_references(params).await
            }
            "textDocument/documentSymbol" => {
                let params: DocumentSymbolParams = serde_json::from_value(req.params).unwrap();
                self.handle_document_symbols(params).await
            }
            "workspace/symbol" => {
                let params: WorkspaceSymbolParams = serde_json::from_value(req.params).unwrap();
                self.handle_workspace_symbols(params).await
            }
            "textDocument/codeAction" => {
                let params: CodeActionParams = serde_json::from_value(req.params).unwrap();
                self.handle_code_actions(params).await
            }
            "textDocument/formatting" => {
                let params: DocumentFormattingParams = serde_json::from_value(req.params).unwrap();
                self.handle_formatting(params).await
            }
            "textDocument/rangeFormatting" => {
                let params: DocumentRangeFormattingParams =
                    serde_json::from_value(req.params).unwrap();
                self.handle_range_formatting(params).await
            }
            "textDocument/semanticTokens/full" => {
                let params: SemanticTokensParams = serde_json::from_value(req.params).unwrap();
                self.handle_semantic_tokens(params).await
            }
            "textDocument/inlayHint" => {
                let params: InlayHintParams = serde_json::from_value(req.params).unwrap();
                self.handle_inlay_hints(params).await
            }
            _ => {
                warn!("Unhandled request method: {}", req.method);
                Err(anyhow::anyhow!("Unimplemented method: {}", req.method))
            }
        };

        let response = match result {
            Ok(value) => lsp_server::Response::new_ok(req.id, value),
            Err(err) => {
                error!("Request failed: {}", err);
                lsp_server::Response::new_err(
                    req.id,
                    lsp_server::ErrorCode::InternalError as i32,
                    err.to_string(),
                )
            }
        };

        if let Err(err) = connection.sender.send(Message::Response(response)) {
            error!("Failed to send response: {}", err);
        }
    }

    async fn handle_notification(&self, connection: &Connection, not: lsp_server::Notification) {
        debug!("Handling notification: {}", not.method);

        match not.method.as_str() {
            "textDocument/didOpen" => {
                let params: DidOpenTextDocumentParams = serde_json::from_value(not.params).unwrap();
                self.handle_did_open(connection, params).await;
            }
            "textDocument/didChange" => {
                let params: DidChangeTextDocumentParams =
                    serde_json::from_value(not.params).unwrap();
                self.handle_did_change(connection, params).await;
            }
            "textDocument/didSave" => {
                let params: DidSaveTextDocumentParams = serde_json::from_value(not.params).unwrap();
                self.handle_did_save(connection, params).await;
            }
            "textDocument/didClose" => {
                let params: DidCloseTextDocumentParams =
                    serde_json::from_value(not.params).unwrap();
                self.handle_did_close(params).await;
            }
            _ => {
                debug!("Unhandled notification: {}", not.method);
            }
        }
    }

    async fn handle_hover(&self, params: HoverParams) -> anyhow::Result<Value> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let path = uri
            .to_file_path()
            .map_err(|_| anyhow::anyhow!("Invalid file path"))?;
        let text_range = self.lsp_position_to_text_range(position, &path).await?;

        if let Some(hover_info) = self.analysis_host.get_hover_info(&path, text_range) {
            let hover = self.hover_info_to_lsp(hover_info);
            Ok(serde_json::to_value(hover)?)
        } else {
            Ok(Value::Null)
        }
    }

    async fn handle_completion(&self, params: CompletionParams) -> anyhow::Result<Value> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        let path = uri
            .to_file_path()
            .map_err(|_| anyhow::anyhow!("Invalid file path"))?;
        let text_range = self.lsp_position_to_text_range(position, &path).await?;

        let completions = self.analysis_host.get_completions(&path, text_range);
        let lsp_completions: Vec<lsp_types::CompletionItem> = completions
            .into_iter()
            .map(|item| self.completion_item_to_lsp(item))
            .collect();

        let response = CompletionResponse::Array(lsp_completions);
        Ok(serde_json::to_value(response)?)
    }

    async fn handle_goto_definition(&self, params: GotoDefinitionParams) -> anyhow::Result<Value> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let path = uri
            .to_file_path()
            .map_err(|_| anyhow::anyhow!("Invalid file path"))?;
        let text_range = self.lsp_position_to_text_range(position, &path).await?;

        if let Some((def_path, def_range)) = self.analysis_host.find_definition(&path, text_range) {
            let def_uri =
                Url::from_file_path(&def_path).map_err(|_| anyhow::anyhow!("Invalid file path"))?;
            let def_position = self.text_range_to_lsp_range(def_range, &def_path).await?;

            let location = Location {
                uri: def_uri,
                range: def_position,
            };

            let response = GotoDefinitionResponse::Scalar(location);
            Ok(serde_json::to_value(response)?)
        } else {
            Ok(Value::Null)
        }
    }

    async fn handle_find_references(&self, params: ReferenceParams) -> anyhow::Result<Value> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        let path = uri
            .to_file_path()
            .map_err(|_| anyhow::anyhow!("Invalid file path"))?;
        let text_range = self.lsp_position_to_text_range(position, &path).await?;

        let references = self.analysis_host.find_references(&path, text_range);
        let mut lsp_references = Vec::new();

        for (ref_path, ref_range) in references {
            let ref_uri =
                Url::from_file_path(&ref_path).map_err(|_| anyhow::anyhow!("Invalid file path"))?;
            let ref_position = self.text_range_to_lsp_range(ref_range, &ref_path).await?;
            lsp_references.push(Location {
                uri: ref_uri,
                range: ref_position,
            });
        }

        Ok(serde_json::to_value(lsp_references)?)
    }

    async fn handle_document_symbols(
        &self,
        _params: DocumentSymbolParams,
    ) -> anyhow::Result<Value> {
        // TODO: Implement document symbols
        Ok(serde_json::to_value(Vec::<DocumentSymbol>::new())?)
    }

    async fn handle_workspace_symbols(
        &self,
        _params: WorkspaceSymbolParams,
    ) -> anyhow::Result<Value> {
        // TODO: Implement workspace symbols
        Ok(serde_json::to_value(Vec::<WorkspaceSymbol>::new())?)
    }

    async fn handle_did_open(&self, connection: &Connection, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        let content = params.text_document.text;

        self.file_versions
            .write()
            .await
            .insert(uri.clone(), version);

        if let Ok(path) = uri.to_file_path() {
            self.analyze_and_publish_diagnostics(connection, &path, &content, version)
                .await;
        }
    }

    async fn handle_did_change(
        &self,
        connection: &Connection,
        params: DidChangeTextDocumentParams,
    ) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;

        self.file_versions
            .write()
            .await
            .insert(uri.clone(), version);

        // Get the updated content (simplified - assumes full document changes)
        if let Some(change) = params.content_changes.into_iter().next() {
            if let Ok(path) = uri.to_file_path() {
                self.analyze_and_publish_diagnostics(connection, &path, &change.text, version)
                    .await;
            }
        }
    }

    async fn handle_did_save(&self, connection: &Connection, params: DidSaveTextDocumentParams) {
        let uri = params.text_document.uri;

        if let Ok(path) = uri.to_file_path() {
            if let Ok(content) = std::fs::read_to_string(&path) {
                let version = self
                    .file_versions
                    .read()
                    .await
                    .get(&uri)
                    .copied()
                    .unwrap_or(0);
                self.analyze_and_publish_diagnostics(connection, &path, &content, version)
                    .await;
            }
        }
    }

    async fn handle_did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        self.file_versions.write().await.remove(&uri);

        if let Ok(path) = uri.to_file_path() {
            self.analysis_host.invalidate_file(&path);
            // Invalidate caches for semantic highlighting
            self.semantic_highlighter
                .write()
                .await
                .invalidate_file(&path);
        }
    }

    async fn analyze_and_publish_diagnostics(
        &self,
        connection: &Connection,
        path: &std::path::Path,
        content: &str,
        version: i32,
    ) {
        match self
            .analysis_host
            .analyze_file(path, content, version)
            .await
        {
            Ok(analysis) => {
                let mut diagnostics = Vec::new();

                // Convert parse errors to diagnostics
                for error in &analysis.parse_errors {
                    let enhanced = self.error_reporter.enhance_parse_error(error, content);
                    diagnostics.push(enhanced.into());
                }

                // Convert elaboration errors to diagnostics (simplified since we store as
                // strings)
                for error_msg in &analysis.elab_errors {
                    let diagnostic = Diagnostic {
                        range: Range {
                            start: Position {
                                line: 0,
                                character: 0,
                            },
                            end: Position {
                                line: 0,
                                character: 0,
                            },
                        },
                        severity: Some(DiagnosticSeverity::ERROR),
                        code: None,
                        code_description: None,
                        source: Some("lean-analyzer".to_string()),
                        message: error_msg.clone(),
                        related_information: None,
                        tags: None,
                        data: None,
                    };
                    diagnostics.push(diagnostic);
                }

                self.publish_diagnostics(connection, path, diagnostics, Some(version))
                    .await;
            }
            Err(err) => {
                error!("Failed to analyze file {}: {}", path.display(), err);
            }
        }
    }

    async fn publish_diagnostics(
        &self,
        connection: &Connection,
        path: &std::path::Path,
        diagnostics: Vec<Diagnostic>,
        version: Option<i32>,
    ) {
        if let Ok(uri) = Url::from_file_path(path) {
            let params = PublishDiagnosticsParams {
                uri,
                diagnostics,
                version,
            };

            let notification = lsp_server::Notification::new(
                "textDocument/publishDiagnostics".to_string(),
                serde_json::to_value(params).unwrap(),
            );

            if let Err(err) = connection.sender.send(Message::Notification(notification)) {
                error!("Failed to publish diagnostics: {}", err);
            }
        }
    }

    // Helper methods for type conversions

    async fn lsp_position_to_text_range(
        &self,
        position: Position,
        _path: &std::path::Path,
    ) -> anyhow::Result<TextRange> {
        // TODO: Implement proper position conversion using file content
        Ok(TextRange::new(
            position.character as usize,
            position.character as usize + 1,
        ))
    }

    async fn text_range_to_lsp_range(
        &self,
        range: TextRange,
        _path: &std::path::Path,
    ) -> anyhow::Result<Range> {
        // TODO: Implement proper range conversion using file content
        Ok(Range {
            start: Position {
                line: 0,
                character: range.start as u32,
            },
            end: Position {
                line: 0,
                character: range.end as u32,
            },
        })
    }

    fn hover_info_to_lsp(&self, hover_info: HoverInfo) -> Hover {
        let mut contents = Vec::new();

        if let Some(signature) = hover_info.signature {
            contents.push(MarkedString::LanguageString(LanguageString {
                language: "lean".to_string(),
                value: signature,
            }));
        }

        if let Some(documentation) = hover_info.documentation {
            contents.push(MarkedString::String(documentation));
        }

        Hover {
            contents: HoverContents::Array(contents),
            range: None,
        }
    }

    fn completion_item_to_lsp(&self, item: CompletionItem) -> lsp_types::CompletionItem {
        lsp_types::CompletionItem {
            label: item.label,
            kind: Some(self.completion_kind_to_lsp(item.kind)),
            detail: item.detail,
            documentation: item.documentation.map(Documentation::String),
            insert_text: item.insert_text,
            ..Default::default()
        }
    }

    fn completion_kind_to_lsp(&self, kind: crate::analysis::CompletionKind) -> CompletionItemKind {
        match kind {
            crate::analysis::CompletionKind::Function => CompletionItemKind::FUNCTION,
            crate::analysis::CompletionKind::Variable => CompletionItemKind::VARIABLE,
            crate::analysis::CompletionKind::Keyword => CompletionItemKind::KEYWORD,
            crate::analysis::CompletionKind::Type => CompletionItemKind::CLASS,
            crate::analysis::CompletionKind::Constructor => CompletionItemKind::CONSTRUCTOR,
            crate::analysis::CompletionKind::Field => CompletionItemKind::FIELD,
            crate::analysis::CompletionKind::Module => CompletionItemKind::MODULE,
            crate::analysis::CompletionKind::Snippet => CompletionItemKind::SNIPPET,
        }
    }

    /// Handle code action requests
    async fn handle_code_actions(&self, params: CodeActionParams) -> anyhow::Result<Value> {
        let file_path = params
            .text_document
            .uri
            .to_file_path()
            .map_err(|_| anyhow::anyhow!("Invalid file path"))?;

        let content = std::fs::read_to_string(&file_path).unwrap_or_else(|_| String::new());

        let actions = self.code_actions.get_code_actions(&params, &content);
        Ok(serde_json::to_value(actions)?)
    }

    /// Handle document formatting requests
    async fn handle_formatting(&self, params: DocumentFormattingParams) -> anyhow::Result<Value> {
        let file_path = params
            .text_document
            .uri
            .to_file_path()
            .map_err(|_| anyhow::anyhow!("Invalid file path"))?;

        let content = std::fs::read_to_string(&file_path).unwrap_or_else(|_| String::new());

        let edits = self.formatter.format_document(&content);
        Ok(serde_json::to_value(edits)?)
    }

    /// Handle range formatting requests
    async fn handle_range_formatting(
        &self,
        params: DocumentRangeFormattingParams,
    ) -> anyhow::Result<Value> {
        let file_path = params
            .text_document
            .uri
            .to_file_path()
            .map_err(|_| anyhow::anyhow!("Invalid file path"))?;

        let content = std::fs::read_to_string(&file_path).unwrap_or_else(|_| String::new());

        let edits = self.formatter.format_range(&content, params.range);
        Ok(serde_json::to_value(edits)?)
    }

    /// Handle semantic tokens requests
    async fn handle_semantic_tokens(&self, params: SemanticTokensParams) -> anyhow::Result<Value> {
        let file_path = params
            .text_document
            .uri
            .to_file_path()
            .map_err(|_| anyhow::anyhow!("Invalid file path"))?;

        let content = std::fs::read_to_string(&file_path).unwrap_or_else(|_| String::new());

        // Parse the file to get syntax tree
        let mut parser = lean_parser::Parser::new(&content);
        let parse_result = parser.module();

        // Generate semantic tokens
        let mut highlighter = self.semantic_highlighter.write().await;
        let tokens = highlighter.analyze_file(&file_path, &content, &parse_result);
        let lsp_tokens = highlighter.to_lsp_tokens(&tokens);

        Ok(serde_json::to_value(lsp_tokens)?)
    }

    /// Handle inlay hints requests
    async fn handle_inlay_hints(&self, params: InlayHintParams) -> anyhow::Result<Value> {
        let file_path = params
            .text_document
            .uri
            .to_file_path()
            .map_err(|_| anyhow::anyhow!("Invalid file path"))?;

        let content = std::fs::read_to_string(&file_path).unwrap_or_else(|_| String::new());

        // Parse the file to get syntax tree
        let mut parser = lean_parser::Parser::new(&content);
        let parse_result = parser.module();

        // Generate inlay hints
        let mut hint_provider = self.inlay_hint_provider.write().await;
        let hints =
            hint_provider.get_hints(&file_path, &content, &parse_result, Some(params.range));

        // Convert to LSP format
        let lsp_hints: Vec<InlayHint> = hints.into_iter().map(|h| h.into()).collect();

        Ok(serde_json::to_value(lsp_hints)?)
    }
}

/// Returns the server capabilities for the LSP initialization
pub fn server_capabilities() -> ServerCapabilities {
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            trigger_characters: Some(vec![".".to_string(), ":".to_string()]),
            all_commit_characters: None,
            work_done_progress_options: WorkDoneProgressOptions::default(),
            completion_item: None,
        }),
        definition_provider: Some(OneOf::Left(true)),
        references_provider: Some(OneOf::Left(true)),
        document_symbol_provider: Some(OneOf::Left(true)),
        workspace_symbol_provider: Some(OneOf::Left(true)),
        code_action_provider: Some(CodeActionProviderCapability::Options(CodeActionOptions {
            code_action_kinds: Some(vec![
                CodeActionKind::QUICKFIX,
                CodeActionKind::REFACTOR,
                CodeActionKind::SOURCE,
                CodeActionKind::SOURCE_ORGANIZE_IMPORTS,
            ]),
            work_done_progress_options: WorkDoneProgressOptions::default(),
            resolve_provider: Some(false),
        })),
        document_formatting_provider: Some(OneOf::Left(true)),
        document_range_formatting_provider: Some(OneOf::Left(true)),
        semantic_tokens_provider: Some(SemanticTokensServerCapabilities::SemanticTokensOptions(
            SemanticTokensOptions {
                work_done_progress_options: WorkDoneProgressOptions::default(),
                legend: SemanticTokensLegend {
                    token_types: vec![
                        SemanticTokenType::NAMESPACE,
                        SemanticTokenType::TYPE,
                        SemanticTokenType::CLASS,
                        SemanticTokenType::ENUM,
                        SemanticTokenType::INTERFACE,
                        SemanticTokenType::STRUCT,
                        SemanticTokenType::TYPE_PARAMETER,
                        SemanticTokenType::PARAMETER,
                        SemanticTokenType::VARIABLE,
                        SemanticTokenType::PROPERTY,
                        SemanticTokenType::ENUM_MEMBER,
                        SemanticTokenType::EVENT,
                        SemanticTokenType::FUNCTION,
                        SemanticTokenType::METHOD,
                        SemanticTokenType::MACRO,
                        SemanticTokenType::KEYWORD,
                        SemanticTokenType::MODIFIER,
                        SemanticTokenType::COMMENT,
                        SemanticTokenType::STRING,
                        SemanticTokenType::NUMBER,
                        SemanticTokenType::REGEXP,
                        SemanticTokenType::OPERATOR,
                    ],
                    token_modifiers: vec![
                        SemanticTokenModifier::DECLARATION,
                        SemanticTokenModifier::DEFINITION,
                        SemanticTokenModifier::READONLY,
                        SemanticTokenModifier::STATIC,
                        SemanticTokenModifier::DEPRECATED,
                        SemanticTokenModifier::ABSTRACT,
                        SemanticTokenModifier::ASYNC,
                        SemanticTokenModifier::MODIFICATION,
                        SemanticTokenModifier::DOCUMENTATION,
                        SemanticTokenModifier::DEFAULT_LIBRARY,
                    ],
                },
                range: Some(true),
                full: Some(SemanticTokensFullOptions::Bool(true)),
            },
        )),
        inlay_hint_provider: Some(OneOf::Left(true)),
        ..Default::default()
    }
}
