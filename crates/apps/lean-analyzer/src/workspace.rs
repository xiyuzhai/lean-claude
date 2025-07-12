//! Workspace management for lean-analyzer

use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use lsp_types::Url;
use tracing::{debug, info};

use crate::{file_system::FileSystem, project::Project};

/// Represents a workspace containing one or more Lean projects
pub struct Workspace {
    root_path: PathBuf,
    file_system: Arc<FileSystem>,
    projects: Vec<Project>,
}

impl Workspace {
    /// Create a new workspace from an optional root URI
    pub fn new(root_uri: Option<&Url>) -> anyhow::Result<Self> {
        let root_path = if let Some(uri) = root_uri {
            uri.to_file_path()
                .map_err(|_| anyhow::anyhow!("Invalid workspace root URI"))?
        } else {
            std::env::current_dir()?
        };

        info!("Creating workspace at: {}", root_path.display());

        let file_system = Arc::new(FileSystem::new());
        let mut workspace = Self {
            root_path: root_path.clone(),
            file_system,
            projects: Vec::new(),
        };

        // Discover projects in the workspace
        workspace.discover_projects()?;

        Ok(workspace)
    }

    /// Get the root path of the workspace
    pub fn root_path(&self) -> &Path {
        &self.root_path
    }

    /// Get the file system instance
    pub fn file_system(&self) -> Arc<FileSystem> {
        Arc::clone(&self.file_system)
    }

    /// Get all projects in the workspace
    pub fn projects(&self) -> &[Project] {
        &self.projects
    }

    /// Find the project that contains the given file
    pub fn find_project_for_file(&self, file_path: &Path) -> Option<&Project> {
        self.projects
            .iter()
            .find(|project| file_path.starts_with(project.root_path()))
    }

    /// Discover Lean projects in the workspace
    fn discover_projects(&mut self) -> anyhow::Result<()> {
        debug!("Discovering projects in workspace");

        // Look for lakefile.lean or lakefile.toml files
        let mut project_roots = Vec::new();
        self.find_project_roots(&self.root_path, &mut project_roots)?;

        // If no project files found, treat the workspace root as a single project
        if project_roots.is_empty() {
            project_roots.push(self.root_path.clone());
        }

        // Create project instances
        for root in project_roots {
            match Project::load(&root) {
                Ok(project) => {
                    info!("Found project: {}", project.name());
                    self.projects.push(project);
                }
                Err(err) => {
                    debug!("Failed to load project at {}: {}", root.display(), err);
                }
            }
        }

        info!("Discovered {} projects", self.projects.len());
        Ok(())
    }

    /// Recursively find project root directories
    #[allow(clippy::only_used_in_recursion)]
    fn find_project_roots(&self, dir: &Path, roots: &mut Vec<PathBuf>) -> anyhow::Result<()> {
        if !dir.is_dir() {
            return Ok(());
        }

        // Check if this directory contains a project file
        let lakefile_lean = dir.join("lakefile.lean");
        let lakefile_toml = dir.join("lakefile.toml");
        let lean_toolchain = dir.join("lean-toolchain");

        if lakefile_lean.exists() || lakefile_toml.exists() || lean_toolchain.exists() {
            roots.push(dir.to_path_buf());
            return Ok(()); // Don't recurse into subdirectories of a project
        }

        // Recursively search subdirectories
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                // Skip common non-project directories
                if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if matches!(name, ".git" | "target" | "build" | ".lake" | "node_modules") {
                        continue;
                    }
                }

                self.find_project_roots(&path, roots)?;
            }
        }

        Ok(())
    }

    /// Reload the workspace (re-discover projects)
    pub fn reload(&mut self) -> anyhow::Result<()> {
        info!("Reloading workspace");
        self.projects.clear();
        self.discover_projects()
    }

    /// Check if a file is a Lean source file
    pub fn is_lean_file(&self, path: &Path) -> bool {
        path.extension()
            .and_then(|ext| ext.to_str())
            .map(|ext| ext == "lean")
            .unwrap_or(false)
    }

    /// Get all Lean files in the workspace
    pub fn lean_files(&self) -> anyhow::Result<Vec<PathBuf>> {
        let mut files = Vec::new();
        self.collect_lean_files(&self.root_path, &mut files)?;
        Ok(files)
    }

    /// Recursively collect Lean files
    fn collect_lean_files(&self, dir: &Path, files: &mut Vec<PathBuf>) -> anyhow::Result<()> {
        if !dir.is_dir() {
            return Ok(());
        }

        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_file() && self.is_lean_file(&path) {
                files.push(path);
            } else if path.is_dir() {
                // Skip build directories and hidden directories
                if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if matches!(name, ".git" | "target" | "build" | ".lake")
                        || name.starts_with('.')
                    {
                        continue;
                    }
                }

                self.collect_lean_files(&path, files)?;
            }
        }

        Ok(())
    }

    /// Watch for file system changes in the workspace
    pub fn start_file_watcher(&self) -> anyhow::Result<()> {
        // TODO: Implement file watching using notify crate
        debug!("File watching not yet implemented");
        Ok(())
    }
}
