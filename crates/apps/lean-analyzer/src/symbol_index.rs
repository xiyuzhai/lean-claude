//! Symbol indexing for fast symbol search and navigation

use std::{collections::HashMap, path::{Path, PathBuf}};

use dashmap::DashMap;
use lean_kernel::Name;
use tracing::debug;

use crate::analysis::{Symbol, SymbolKind, TextRange};

/// Global symbol index for fast lookups
pub struct SymbolIndex {
    /// Symbol name to locations mapping
    symbols: DashMap<String, Vec<SymbolLocation>>,
    /// File to symbols mapping
    file_symbols: DashMap<PathBuf, Vec<IndexedSymbol>>,
    /// Fuzzy search index
    fuzzy_index: FuzzyIndex,
}

/// Location of a symbol
#[derive(Debug, Clone)]
pub struct SymbolLocation {
    pub file_path: PathBuf,
    pub range: TextRange,
    pub kind: SymbolKind,
    pub definition: bool, // true if this is the definition, false if reference
}

/// Symbol with additional indexing information
#[derive(Debug, Clone)]
pub struct IndexedSymbol {
    pub symbol: Symbol,
    pub qualified_name: String,
    pub namespace: Vec<String>,
}

/// Fuzzy search index for symbol names
struct FuzzyIndex {
    /// All symbol names for fuzzy matching
    names: Vec<String>,
    /// Mapping from name index to symbol locations
    name_to_locations: HashMap<usize, Vec<SymbolLocation>>,
}

impl SymbolIndex {
    /// Create a new symbol index
    pub fn new() -> Self {
        Self {
            symbols: DashMap::new(),
            file_symbols: DashMap::new(),
            fuzzy_index: FuzzyIndex::new(),
        }
    }

    /// Update symbols for a file
    pub fn update_file(&mut self, file_path: &PathBuf, symbols: &[Symbol]) {
        debug!("Updating symbol index for: {}", file_path.display());

        // Remove old symbols for this file
        if let Some(old_symbols) = self.file_symbols.get(file_path) {
            for indexed_symbol in old_symbols.iter() {
                self.remove_symbol(&indexed_symbol.qualified_name, file_path);
            }
        }

        // Add new symbols
        let mut indexed_symbols = Vec::new();
        let mut current_namespace = Vec::new();

        for symbol in symbols {
            let indexed_symbol = self.create_indexed_symbol(symbol, &current_namespace);
            self.add_symbol(&indexed_symbol, file_path);
            indexed_symbols.push(indexed_symbol);

            // Update namespace if this is a namespace symbol
            if symbol.kind == SymbolKind::Namespace {
                current_namespace.push(self.name_to_string(&symbol.name));
            }
        }

        self.file_symbols.insert(file_path.clone(), indexed_symbols);
        self.rebuild_fuzzy_index();
    }

    /// Find the definition of a symbol
    pub fn find_definition(&self, name: &Name) -> Option<(PathBuf, TextRange)> {
        let name_str = self.name_to_string(name);

        if let Some(locations) = self.symbols.get(&name_str) {
            // Look for the definition location
            for location in locations.iter() {
                if location.definition {
                    return Some((location.file_path.clone(), location.range));
                }
            }

            // If no definition found, return the first occurrence
            if let Some(first) = locations.first() {
                return Some((first.file_path.clone(), first.range));
            }
        }

        None
    }

    /// Find all references to a symbol
    pub fn find_references(&self, name: &Name) -> Vec<(PathBuf, TextRange)> {
        let name_str = self.name_to_string(name);

        if let Some(locations) = self.symbols.get(&name_str) {
            locations
                .iter()
                .map(|loc| (loc.file_path.clone(), loc.range))
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Search for symbols by name (fuzzy search)
    pub fn search_symbols(&self, query: &str) -> Vec<SymbolSearchResult> {
        self.fuzzy_index.search(query, 50)
    }

    /// Get all symbols in a file
    pub fn file_symbols(&self, file_path: &PathBuf) -> Vec<IndexedSymbol> {
        self.file_symbols
            .get(file_path)
            .map(|symbols| symbols.clone())
            .unwrap_or_default()
    }

    /// Get symbols by kind
    pub fn symbols_by_kind(&self, kind: SymbolKind) -> Vec<SymbolLocation> {
        let mut results = Vec::new();

        for entry in self.symbols.iter() {
            for location in entry.value().iter() {
                if location.kind == kind {
                    results.push(location.clone());
                }
            }
        }

        results
    }

    /// Get all symbols in a namespace
    pub fn symbols_in_namespace(&self, namespace: &[String]) -> Vec<IndexedSymbol> {
        let mut results = Vec::new();

        for entry in self.file_symbols.iter() {
            for symbol in entry.value().iter() {
                if symbol.namespace.len() >= namespace.len() {
                    let symbol_ns = &symbol.namespace[..namespace.len()];
                    if symbol_ns == namespace {
                        results.push(symbol.clone());
                    }
                }
            }
        }

        results
    }

    /// Remove a file from the index
    pub fn remove_file(&mut self, file_path: &PathBuf) {
        debug!("Removing file from symbol index: {}", file_path.display());

        if let Some(symbols) = self.file_symbols.remove(file_path) {
            for indexed_symbol in symbols.1.iter() {
                self.remove_symbol(&indexed_symbol.qualified_name, file_path);
            }
        }

        self.rebuild_fuzzy_index();
    }

    /// Clear the entire index
    pub fn clear(&mut self) {
        self.symbols.clear();
        self.file_symbols.clear();
        self.fuzzy_index = FuzzyIndex::new();
    }

    /// Get index statistics
    pub fn stats(&self) -> IndexStats {
        let total_symbols = self.symbols.len();
        let total_files = self.file_symbols.len();
        let total_locations: usize = self.symbols.iter().map(|entry| entry.value().len()).sum();

        IndexStats {
            total_symbols,
            total_files,
            total_locations,
        }
    }

    // Private helper methods

    fn create_indexed_symbol(&self, symbol: &Symbol, namespace: &[String]) -> IndexedSymbol {
        let name_str = self.name_to_string(&symbol.name);
        let qualified_name = if namespace.is_empty() {
            name_str
        } else {
            format!("{}.{}", namespace.join("."), name_str)
        };

        IndexedSymbol {
            symbol: symbol.clone(),
            qualified_name,
            namespace: namespace.to_vec(),
        }
    }

    fn add_symbol(&self, indexed_symbol: &IndexedSymbol, file_path: &Path) {
        let location = SymbolLocation {
            file_path: file_path.to_path_buf(),
            range: indexed_symbol.symbol.range,
            kind: indexed_symbol.symbol.kind.clone(),
            definition: indexed_symbol.symbol.definition_range.is_some(),
        };

        self.symbols
            .entry(indexed_symbol.qualified_name.clone())
            .or_default()
            .push(location);
    }

    fn remove_symbol(&self, qualified_name: &str, file_path: &PathBuf) {
        if let Some(mut locations) = self.symbols.get_mut(qualified_name) {
            locations.retain(|loc| loc.file_path != *file_path);

            // Remove the entry if no locations remain
            if locations.is_empty() {
                drop(locations); // Drop the mutable reference
                self.symbols.remove(qualified_name);
            }
        }
    }

    fn rebuild_fuzzy_index(&mut self) {
        let mut names = Vec::new();
        let mut name_to_locations = HashMap::new();

        for entry in self.symbols.iter() {
            let name = entry.key().clone();
            let locations = entry.value().clone();

            let index = names.len();
            names.push(name);
            name_to_locations.insert(index, locations);
        }

        self.fuzzy_index = FuzzyIndex {
            names,
            name_to_locations,
        };
    }

    fn name_to_string(&self, name: &Name) -> String {
        // TODO: Implement proper name formatting
        format!("{name:?}")
    }
}

impl FuzzyIndex {
    fn new() -> Self {
        Self {
            names: Vec::new(),
            name_to_locations: HashMap::new(),
        }
    }

    fn search(&self, query: &str, limit: usize) -> Vec<SymbolSearchResult> {
        let mut results = Vec::new();
        let query_lower = query.to_lowercase();

        for (index, name) in self.names.iter().enumerate() {
            let score = self.fuzzy_score(&query_lower, &name.to_lowercase());
            if score > 0.0 {
                if let Some(locations) = self.name_to_locations.get(&index) {
                    for location in locations {
                        results.push(SymbolSearchResult {
                            name: name.clone(),
                            location: location.clone(),
                            score,
                        });
                    }
                }
            }
        }

        // Sort by score (descending) and limit results
        results.sort_by(|a, b| b.score.partial_cmp(&a.score).unwrap());
        results.truncate(limit);
        results
    }

    fn fuzzy_score(&self, query: &str, target: &str) -> f64 {
        if query.is_empty() {
            return 0.0;
        }

        if target.contains(query) {
            // Exact substring match gets high score
            return 0.9;
        }

        // Simple fuzzy matching: check if all characters are present in order
        let mut query_chars = query.chars();
        let mut current_char = query_chars.next();
        let mut matched_chars = 0;

        for target_char in target.chars() {
            if let Some(q_char) = current_char {
                if q_char == target_char {
                    matched_chars += 1;
                    current_char = query_chars.next();
                    if current_char.is_none() {
                        break;
                    }
                }
            }
        }

        if matched_chars == query.len() {
            // All characters matched, score based on length ratio
            (matched_chars as f64) / (target.len() as f64)
        } else {
            0.0
        }
    }
}

/// Symbol search result
#[derive(Debug, Clone)]
pub struct SymbolSearchResult {
    pub name: String,
    pub location: SymbolLocation,
    pub score: f64,
}

/// Index statistics
#[derive(Debug, Clone)]
pub struct IndexStats {
    pub total_symbols: usize,
    pub total_files: usize,
    pub total_locations: usize,
}

impl Default for SymbolIndex {
    fn default() -> Self {
        Self::new()
    }
}

// Helper trait for Name creation in tests
#[allow(dead_code)]
trait NameFromStr {
    fn from_str(s: &str) -> Self;
}

impl NameFromStr for Name {
    fn from_str(_s: &str) -> Self {
        // TODO: Implement proper name creation from string
        // For now, return a placeholder
        unsafe { std::mem::zeroed() }
    }
}

#[cfg(test)]
mod tests {
    use lean_kernel::Name;

    use super::*;

    #[test]
    fn test_fuzzy_search() {
        let index = FuzzyIndex::new();

        // Test exact match
        assert!(index.fuzzy_score("test", "test") > 0.8);

        // Test substring match
        assert!(index.fuzzy_score("test", "testing") > 0.7);

        // Test fuzzy match
        assert!(index.fuzzy_score("tst", "test") > 0.0);

        // Test no match
        assert_eq!(index.fuzzy_score("xyz", "test"), 0.0);
    }

    #[test]
    fn test_symbol_index_operations() {
        let mut index = SymbolIndex::new();
        let file_path = PathBuf::from("test.lean");

        // Create test symbols
        let symbols = vec![Symbol {
            name: Name::from_str("test_function"),
            kind: SymbolKind::Definition,
            range: TextRange::new(0, 10),
            definition_range: Some(TextRange::new(0, 10)),
            signature: Some("def test_function : Nat".to_string()),
            documentation: None,
        }];

        // Update file symbols
        index.update_file(&file_path, &symbols);

        // Test finding definition
        let name = Name::from_str("test_function");
        assert!(index.find_definition(&name).is_some());

        // Test file symbols
        let file_symbols = index.file_symbols(&file_path);
        assert_eq!(file_symbols.len(), 1);

        // Test removing file
        index.remove_file(&file_path);
        assert!(index.find_definition(&name).is_none());
    }
}
