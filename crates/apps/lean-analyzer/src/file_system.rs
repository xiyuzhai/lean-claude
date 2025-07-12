//! File system abstraction for lean-analyzer

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    sync::mpsc,
    time::SystemTime,
};

use notify::{Config, Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use parking_lot::RwLock;
use tracing::{debug, error, info};

/// File system abstraction that tracks file contents and changes
pub struct FileSystem {
    files: RwLock<HashMap<PathBuf, FileEntry>>,
    watchers: RwLock<HashMap<PathBuf, RecommendedWatcher>>,
    change_sender: Option<mpsc::Sender<FileSystemEvent>>,
}

/// Represents a file entry in the file system
#[derive(Debug, Clone)]
struct FileEntry {
    #[allow(dead_code)]
    path: PathBuf,
    content: String,
    version: i32,
    last_modified: SystemTime,
}

/// File system events
#[derive(Debug, Clone)]
pub enum FileSystemEvent {
    FileCreated(PathBuf),
    FileModified(PathBuf),
    FileDeleted(PathBuf),
    DirectoryCreated(PathBuf),
    DirectoryDeleted(PathBuf),
}

impl FileSystem {
    /// Create a new file system instance
    pub fn new() -> Self {
        Self {
            files: RwLock::new(HashMap::new()),
            watchers: RwLock::new(HashMap::new()),
            change_sender: None,
        }
    }

    /// Create a new file system with change notifications
    pub fn with_change_notifications(sender: mpsc::Sender<FileSystemEvent>) -> Self {
        Self {
            files: RwLock::new(HashMap::new()),
            watchers: RwLock::new(HashMap::new()),
            change_sender: Some(sender),
        }
    }

    /// Read a file's content
    pub fn read_file(&self, path: &Path) -> anyhow::Result<String> {
        // Check if we have the file cached
        {
            let files = self.files.read();
            if let Some(entry) = files.get(path) {
                // Check if the cached version is still current
                if let Ok(metadata) = std::fs::metadata(path) {
                    if let Ok(modified) = metadata.modified() {
                        if modified <= entry.last_modified {
                            return Ok(entry.content.clone());
                        }
                    }
                }
            }
        }

        // Read from disk and cache
        let content = std::fs::read_to_string(path)?;
        let metadata = std::fs::metadata(path)?;
        let last_modified = metadata.modified().unwrap_or(SystemTime::now());

        let entry = FileEntry {
            path: path.to_path_buf(),
            content: content.clone(),
            version: 1,
            last_modified,
        };

        self.files.write().insert(path.to_path_buf(), entry);

        debug!("Read file: {}", path.display());
        Ok(content)
    }

    /// Write content to a file (for testing purposes)
    pub fn write_file(&self, path: &Path, content: &str) -> anyhow::Result<()> {
        std::fs::write(path, content)?;

        let entry = FileEntry {
            path: path.to_path_buf(),
            content: content.to_string(),
            version: self.get_file_version(path) + 1,
            last_modified: SystemTime::now(),
        };

        self.files.write().insert(path.to_path_buf(), entry);

        if let Some(sender) = &self.change_sender {
            let _ = sender.send(FileSystemEvent::FileModified(path.to_path_buf()));
        }

        debug!("Wrote file: {}", path.display());
        Ok(())
    }

    /// Update file content in memory (e.g., from LSP changes)
    pub fn update_file_content(&self, path: &Path, content: String, version: i32) {
        let entry = FileEntry {
            path: path.to_path_buf(),
            content,
            version,
            last_modified: SystemTime::now(),
        };

        self.files.write().insert(path.to_path_buf(), entry);

        if let Some(sender) = &self.change_sender {
            let _ = sender.send(FileSystemEvent::FileModified(path.to_path_buf()));
        }

        debug!(
            "Updated file content: {} (version {})",
            path.display(),
            version
        );
    }

    /// Get the current version of a file
    pub fn get_file_version(&self, path: &Path) -> i32 {
        self.files
            .read()
            .get(path)
            .map(|entry| entry.version)
            .unwrap_or(0)
    }

    /// Check if a file exists
    pub fn file_exists(&self, path: &Path) -> bool {
        path.exists()
    }

    /// List all files in a directory
    pub fn list_directory(&self, path: &Path) -> anyhow::Result<Vec<PathBuf>> {
        let mut files = Vec::new();

        for entry in std::fs::read_dir(path)? {
            let entry = entry?;
            files.push(entry.path());
        }

        Ok(files)
    }

    /// Find all files matching a pattern
    pub fn find_files(&self, root: &Path, pattern: &str) -> anyhow::Result<Vec<PathBuf>> {
        let mut files = Vec::new();
        self.find_files_recursive(root, pattern, &mut files)?;
        Ok(files)
    }

    /// Recursively find files matching a pattern
    #[allow(clippy::only_used_in_recursion)]
    fn find_files_recursive(
        &self,
        dir: &Path,
        pattern: &str,
        files: &mut Vec<PathBuf>,
    ) -> anyhow::Result<()> {
        if !dir.is_dir() {
            return Ok(());
        }

        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_file() {
                if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if Self::matches_pattern(name, pattern) {
                        files.push(path);
                    }
                }
            } else if path.is_dir() {
                // Skip hidden directories and common build directories
                if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if !name.starts_with('.') && !matches!(name, "target" | "build" | ".lake") {
                        self.find_files_recursive(&path, pattern, files)?;
                    }
                }
            }
        }

        Ok(())
    }

    /// Simple pattern matching (supports * wildcards)
    fn matches_pattern(name: &str, pattern: &str) -> bool {
        if pattern == "*" {
            return true;
        }

        if pattern.contains('*') {
            // Split pattern by * and check if all parts are present in order
            let parts: Vec<&str> = pattern.split('*').collect();
            let mut pos = 0;

            for (i, part) in parts.iter().enumerate() {
                if part.is_empty() {
                    continue;
                }

                if let Some(found_pos) = name[pos..].find(part) {
                    pos += found_pos + part.len();
                } else {
                    return false;
                }

                // If this is the last part and doesn't end with *, check suffix
                if i == parts.len() - 1 && !pattern.ends_with('*') {
                    return name.ends_with(part);
                }
            }

            true
        } else {
            name == pattern
        }
    }

    /// Start watching a directory for changes
    pub fn watch_directory(&self, path: &Path) -> anyhow::Result<()> {
        if self.change_sender.is_none() {
            return Err(anyhow::anyhow!(
                "File system not configured for change notifications"
            ));
        }

        let sender = self.change_sender.as_ref().unwrap().clone();
        let path_buf = path.to_path_buf();

        let mut watcher = RecommendedWatcher::new(
            move |res: Result<Event, notify::Error>| {
                match res {
                    Ok(event) => {
                        let fs_event = match event.kind {
                            EventKind::Create(_) => {
                                if let Some(path) = event.paths.first() {
                                    if path.is_file() {
                                        Some(FileSystemEvent::FileCreated(path.clone()))
                                    } else {
                                        Some(FileSystemEvent::DirectoryCreated(path.clone()))
                                    }
                                } else {
                                    None
                                }
                            }
                            EventKind::Modify(_) => event
                                .paths
                                .first()
                                .map(|path| FileSystemEvent::FileModified(path.clone())),
                            EventKind::Remove(_) => {
                                event.paths.first().map(|path| FileSystemEvent::FileDeleted(path.clone()))
                            }
                            _ => None,
                        };

                        if let Some(fs_event) = fs_event {
                            if let Err(err) = sender.send(fs_event) {
                                error!("Failed to send file system event: {}", err);
                            }
                        }
                    }
                    Err(err) => {
                        error!("File watcher error: {}", err);
                    }
                }
            },
            Config::default(),
        )?;

        watcher.watch(path, RecursiveMode::Recursive)?;
        self.watchers.write().insert(path_buf.clone(), watcher);

        info!("Started watching directory: {}", path.display());
        Ok(())
    }

    /// Stop watching a directory
    pub fn stop_watching(&self, path: &Path) {
        if self.watchers.write().remove(path).is_some() {
            info!("Stopped watching directory: {}", path.display());
        }
    }

    /// Invalidate cached file content
    pub fn invalidate_file(&self, path: &Path) {
        self.files.write().remove(path);
        debug!("Invalidated cached file: {}", path.display());
    }

    /// Clear all cached files
    pub fn clear_cache(&self) {
        self.files.write().clear();
        info!("Cleared file cache");
    }

    /// Get statistics about cached files
    pub fn cache_stats(&self) -> (usize, usize) {
        let files = self.files.read();
        let total_files = files.len();
        let total_size: usize = files.values().map(|entry| entry.content.len()).sum();
        (total_files, total_size)
    }
}

impl Default for FileSystem {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::mpsc;

    use tempfile::TempDir;

    use super::*;

    #[test]
    fn test_pattern_matching() {
        assert!(FileSystem::matches_pattern("file.lean", "*.lean"));
        assert!(FileSystem::matches_pattern("file.lean", "file.*"));
        assert!(FileSystem::matches_pattern("file.lean", "*"));
        assert!(FileSystem::matches_pattern("file.lean", "file.lean"));
        assert!(!FileSystem::matches_pattern("file.rs", "*.lean"));
    }

    #[test]
    fn test_file_operations() -> anyhow::Result<()> {
        let temp_dir = TempDir::new()?;
        let file_path = temp_dir.path().join("test.lean");

        let (sender, _receiver) = mpsc::channel();
        let fs = FileSystem::with_change_notifications(sender);

        // Write a file
        let content = "def hello : String := \"world\"";
        fs.write_file(&file_path, content)?;

        // Read it back
        let read_content = fs.read_file(&file_path)?;
        assert_eq!(content, read_content);

        // Check version
        assert_eq!(fs.get_file_version(&file_path), 1);

        // Update content
        let new_content = "def hello : String := \"universe\"";
        fs.update_file_content(&file_path, new_content.to_string(), 2);

        // Check updated version
        assert_eq!(fs.get_file_version(&file_path), 2);

        Ok(())
    }
}
