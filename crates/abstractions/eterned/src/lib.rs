#![feature(let_chains)]

use dashmap::DashMap;
use once_cell::sync::Lazy;
use sha2::{Digest, Sha512};
use std::sync::Arc;

pub use eterned_macros::eterned;

pub static ETERNER_DB: Lazy<EternerDb> = Lazy::new(EternerDb::default);

#[derive(Default)]
pub struct EternerDb {
    strings: DashMap<String, Arc<String>>,
}

impl EternerDb {
    pub fn intern(&self, s: impl Into<String>) -> Arc<String> {
        let s = s.into();
        if let Some(interned) = self.strings.get(&s) {
            interned.clone()
        } else {
            let arc = Arc::new(s.clone());
            self.strings.insert(s, arc.clone());
            arc
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BaseCoword {
    data: Arc<String>,
}

impl BaseCoword {
    pub fn new(s: impl Into<String>) -> Self {
        Self {
            data: ETERNER_DB.intern(s),
        }
    }

    pub fn as_str(&self) -> &str {
        &self.data
    }

    pub fn sha512_hash(&self) -> [u8; 64] {
        let mut hasher = Sha512::new();
        hasher.update(self.as_str().as_bytes());
        hasher.finalize().into()
    }
}

impl From<&str> for BaseCoword {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl From<String> for BaseCoword {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

impl std::fmt::Display for BaseCoword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    #[test]
    fn test_interning() {
        let s1 = BaseCoword::new("hello");
        let s2 = BaseCoword::new("hello");
        let s3 = BaseCoword::new("world");

        assert!(Arc::ptr_eq(&s1.data, &s2.data));
        assert!(!Arc::ptr_eq(&s1.data, &s3.data));
    }

    #[test]
    fn test_display() {
        let s = BaseCoword::new("test string");
        expect![[r#"test string"#]].assert_eq(&s.to_string());
    }
}