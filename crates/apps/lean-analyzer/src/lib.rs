//! Lean Analyzer - Language Server Protocol implementation for Lean 4
//!
//! This crate provides IDE support for Lean 4, inspired by rust-analyzer.
//! It implements the Language Server Protocol (LSP) to provide features like:
//! - Superior error messages with detailed explanations and suggestions
//! - Syntax highlighting with semantic information
//! - Hover information with type and documentation
//! - Go to definition and find references
//! - Smart completions with context awareness
//! - Real-time diagnostics with fix suggestions
//! - Symbol search and workspace navigation

pub mod analysis;
pub mod code_actions;
pub mod diagnostics;
pub mod error_reporting;
pub mod file_system;
pub mod formatting;
pub mod lsp;
pub mod project;
pub mod symbol_index;
pub mod workspace;

use std::sync::Arc;

pub use analysis::AnalysisHost;
pub use lsp::LeanLanguageServer;
pub use project::Project;
use tracing::info;
pub use workspace::Workspace;

/// Main entry point for the lean-analyzer
pub async fn run_server() -> anyhow::Result<()> {
    info!("Starting Lean Language Server");

    let (connection, io_threads) = lsp_server::Connection::stdio();
    let capabilities = lsp::server_capabilities();

    let initialization_params = connection.initialize(serde_json::to_value(capabilities)?)?;
    let params: lsp_types::InitializeParams = serde_json::from_value(initialization_params)?;

    let workspace = Arc::new(Workspace::new(params.root_uri.as_ref())?);
    let server = LeanLanguageServer::new(workspace);

    server.run(connection).await?;

    io_threads.join()?;
    info!("Lean Language Server shut down");

    Ok(())
}
