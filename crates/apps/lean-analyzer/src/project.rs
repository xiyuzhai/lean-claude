//! Project representation and management

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

use tracing::{debug, info};

/// Represents a single Lean project
#[derive(Debug, Clone)]
pub struct Project {
    name: String,
    root_path: PathBuf,
    config: ProjectConfig,
    dependencies: Vec<Dependency>,
    source_dirs: Vec<PathBuf>,
}

/// Project configuration parsed from lakefile.lean or lakefile.toml
#[derive(Debug, Clone)]
pub struct ProjectConfig {
    pub lean_version: Option<String>,
    pub build_dir: PathBuf,
    pub lib_dirs: Vec<PathBuf>,
    pub more_server_args: Vec<String>,
    pub custom_settings: HashMap<String, String>,
}

/// External dependency of a project
#[derive(Debug, Clone)]
pub struct Dependency {
    pub name: String,
    pub source: DependencySource,
    pub path: Option<PathBuf>,
}

/// Source of a dependency
#[derive(Debug, Clone)]
pub enum DependencySource {
    Git { url: String, rev: Option<String> },
    Path { path: PathBuf },
    Local,
}

impl Project {
    /// Load a project from the given root directory
    pub fn load(root_path: &Path) -> anyhow::Result<Self> {
        debug!("Loading project from: {}", root_path.display());

        let name = root_path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("unnamed")
            .to_string();

        let config = Self::load_config(root_path)?;
        let dependencies = Self::discover_dependencies(root_path)?;
        let source_dirs = Self::discover_source_directories(root_path)?;

        let project = Self {
            name,
            root_path: root_path.to_path_buf(),
            config,
            dependencies,
            source_dirs,
        };

        info!(
            "Loaded project '{}' with {} dependencies",
            project.name,
            project.dependencies.len()
        );
        Ok(project)
    }

    /// Get the project name
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the project root path
    pub fn root_path(&self) -> &Path {
        &self.root_path
    }

    /// Get the project configuration
    pub fn config(&self) -> &ProjectConfig {
        &self.config
    }

    /// Get project dependencies
    pub fn dependencies(&self) -> &[Dependency] {
        &self.dependencies
    }

    /// Get source directories
    pub fn source_dirs(&self) -> &[PathBuf] {
        &self.source_dirs
    }

    /// Get the Lean version for this project
    pub fn lean_version(&self) -> Option<&str> {
        self.config.lean_version.as_deref()
    }

    /// Check if a file belongs to this project
    pub fn contains_file(&self, file_path: &Path) -> bool {
        file_path.starts_with(&self.root_path)
    }

    /// Get all Lean files in this project
    pub fn lean_files(&self) -> anyhow::Result<Vec<PathBuf>> {
        let mut files = Vec::new();

        for source_dir in &self.source_dirs {
            self.collect_lean_files_in_dir(source_dir, &mut files)?;
        }

        Ok(files)
    }

    /// Load project configuration from lakefile.lean or lakefile.toml
    fn load_config(root_path: &Path) -> anyhow::Result<ProjectConfig> {
        let mut config = ProjectConfig {
            lean_version: None,
            build_dir: root_path.join(".lake").join("build"),
            lib_dirs: vec![root_path.join(".lake").join("packages")],
            more_server_args: Vec::new(),
            custom_settings: HashMap::new(),
        };

        // Try to read lean-toolchain file for version
        let toolchain_file = root_path.join("lean-toolchain");
        if toolchain_file.exists() {
            if let Ok(content) = std::fs::read_to_string(&toolchain_file) {
                config.lean_version = Some(content.trim().to_string());
            }
        }

        // Try to parse lakefile.lean
        let lakefile_lean = root_path.join("lakefile.lean");
        if lakefile_lean.exists() {
            if let Ok(content) = std::fs::read_to_string(&lakefile_lean) {
                Self::parse_lakefile_lean(&content, &mut config)?;
            }
        }

        // Try to parse lakefile.toml
        let lakefile_toml = root_path.join("lakefile.toml");
        if lakefile_toml.exists() {
            if let Ok(content) = std::fs::read_to_string(&lakefile_toml) {
                Self::parse_lakefile_toml(&content, &mut config)?;
            }
        }

        Ok(config)
    }

    /// Parse lakefile.lean content (simplified parser)
    fn parse_lakefile_lean(content: &str, config: &mut ProjectConfig) -> anyhow::Result<()> {
        // TODO: Implement proper lakefile.lean parsing
        // For now, just extract some basic patterns

        for line in content.lines() {
            let line = line.trim();

            // Look for server args
            if line.contains("moreServerArgs") || line.contains("more_server_args") {
                // Extract server arguments - simplified
                if let Some(start) = line.find('[') {
                    if let Some(end) = line.find(']') {
                        let args_str = &line[start + 1..end];
                        for arg in args_str.split(',') {
                            let arg = arg.trim().trim_matches('"').trim_matches('\'');
                            if !arg.is_empty() {
                                config.more_server_args.push(arg.to_string());
                            }
                        }
                    }
                }
            }
        }

        debug!(
            "Parsed lakefile.lean with {} server args",
            config.more_server_args.len()
        );
        Ok(())
    }

    /// Parse lakefile.toml content
    fn parse_lakefile_toml(content: &str, config: &mut ProjectConfig) -> anyhow::Result<()> {
        // TODO: Implement TOML parsing using a proper TOML library
        // For now, just extract basic key-value pairs

        for line in content.lines() {
            let line = line.trim();
            if let Some(eq_pos) = line.find('=') {
                let key = line[..eq_pos].trim();
                let value = line[eq_pos + 1..]
                    .trim()
                    .trim_matches('"')
                    .trim_matches('\'');

                match key {
                    "lean_version" => config.lean_version = Some(value.to_string()),
                    _ => {
                        config
                            .custom_settings
                            .insert(key.to_string(), value.to_string());
                    }
                }
            }
        }

        debug!(
            "Parsed lakefile.toml with {} custom settings",
            config.custom_settings.len()
        );
        Ok(())
    }

    /// Discover project dependencies
    fn discover_dependencies(root_path: &Path) -> anyhow::Result<Vec<Dependency>> {
        let mut dependencies = Vec::new();

        // Check for lake-manifest.json
        let manifest_file = root_path.join("lake-manifest.json");
        if manifest_file.exists() {
            if let Ok(content) = std::fs::read_to_string(&manifest_file) {
                dependencies.extend(Self::parse_lake_manifest(&content)?);
            }
        }

        // Check for .lake/packages directory
        let packages_dir = root_path.join(".lake").join("packages");
        if packages_dir.exists() {
            for entry in std::fs::read_dir(&packages_dir)? {
                let entry = entry?;
                if entry.path().is_dir() {
                    if let Some(name) = entry.file_name().to_str() {
                        dependencies.push(Dependency {
                            name: name.to_string(),
                            source: DependencySource::Local,
                            path: Some(entry.path()),
                        });
                    }
                }
            }
        }

        Ok(dependencies)
    }

    /// Parse lake-manifest.json to extract dependencies
    fn parse_lake_manifest(_content: &str) -> anyhow::Result<Vec<Dependency>> {
        // TODO: Implement proper JSON parsing
        // For now, return empty dependencies
        Ok(Vec::new())
    }

    /// Discover source directories in the project
    fn discover_source_directories(root_path: &Path) -> anyhow::Result<Vec<PathBuf>> {
        let mut source_dirs = Vec::new();

        // Common source directory names
        let common_dirs = ["src", "lib", "Lib", ".", "Source"];

        for dir_name in &common_dirs {
            let dir_path = root_path.join(dir_name);
            if dir_path.exists() && dir_path.is_dir() {
                // Check if it contains any .lean files
                if Self::contains_lean_files(&dir_path)? {
                    source_dirs.push(dir_path);
                }
            }
        }

        // If no source directories found, use the root directory
        if source_dirs.is_empty() {
            source_dirs.push(root_path.to_path_buf());
        }

        Ok(source_dirs)
    }

    /// Check if a directory contains any .lean files
    fn contains_lean_files(dir: &Path) -> anyhow::Result<bool> {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_file() {
                if let Some(ext) = path.extension() {
                    if ext == "lean" {
                        return Ok(true);
                    }
                }
            } else if path.is_dir() {
                // Don't recurse too deeply
                if Self::contains_lean_files(&path)? {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    /// Collect all .lean files in a directory recursively
    #[allow(clippy::only_used_in_recursion)]
    fn collect_lean_files_in_dir(
        &self,
        dir: &Path,
        files: &mut Vec<PathBuf>,
    ) -> anyhow::Result<()> {
        if !dir.exists() || !dir.is_dir() {
            return Ok(());
        }

        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_file() {
                if let Some(ext) = path.extension() {
                    if ext == "lean" {
                        files.push(path);
                    }
                }
            } else if path.is_dir() {
                // Skip build directories
                if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if matches!(name, ".lake" | "build" | ".git") {
                        continue;
                    }
                }

                self.collect_lean_files_in_dir(&path, files)?;
            }
        }

        Ok(())
    }
}

impl Default for ProjectConfig {
    fn default() -> Self {
        Self {
            lean_version: None,
            build_dir: PathBuf::from(".lake/build"),
            lib_dirs: vec![PathBuf::from(".lake/packages")],
            more_server_args: Vec::new(),
            custom_settings: HashMap::new(),
        }
    }
}
