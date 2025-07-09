use std::sync::atomic::{AtomicU64, Ordering};

use eterned::BaseCoword;

/// Generates fresh names for hygienic macro expansion
pub struct NameGenerator {
    counter: AtomicU64,
}

impl NameGenerator {
    pub fn new() -> Self {
        Self {
            counter: AtomicU64::new(0),
        }
    }

    /// Generate a fresh name based on a base name
    pub fn fresh_name(&self, base: &str) -> BaseCoword {
        let id = self.counter.fetch_add(1, Ordering::SeqCst);
        BaseCoword::new(format!("{base}.{id}"))
    }

    /// Generate a fresh name for macro-introduced bindings
    pub fn fresh_macro_name(&self) -> BaseCoword {
        self.fresh_name("_macro")
    }
}

impl Default for NameGenerator {
    fn default() -> Self {
        Self::new()
    }
}

/// Context for hygienic expansion
#[derive(Clone)]
pub struct HygieneContext {
    /// Current expansion depth (for limiting recursion)
    pub depth: usize,
    /// Maximum allowed expansion depth
    pub max_depth: usize,
    /// Name generator for fresh names
    pub name_gen: std::sync::Arc<NameGenerator>,
}

impl HygieneContext {
    pub fn new() -> Self {
        Self {
            depth: 0,
            max_depth: 1000,
            name_gen: std::sync::Arc::new(NameGenerator::new()),
        }
    }

    /// Enter a new expansion level
    pub fn enter_expansion(&self) -> Option<Self> {
        if self.depth >= self.max_depth {
            None
        } else {
            Some(Self {
                depth: self.depth + 1,
                max_depth: self.max_depth,
                name_gen: self.name_gen.clone(),
            })
        }
    }

    /// Generate a fresh name
    pub fn fresh_name(&self, base: &str) -> BaseCoword {
        self.name_gen.fresh_name(base)
    }
}

impl Default for HygieneContext {
    fn default() -> Self {
        Self::new()
    }
}
