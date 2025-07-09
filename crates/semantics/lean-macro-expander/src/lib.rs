pub mod environment;
pub mod error;
pub mod expander;
pub mod hygiene;
pub mod pattern;

pub use environment::{MacroDefinition, MacroEnvironment};
pub use error::{ExpansionError, ExpansionResult};
pub use expander::MacroExpander;

#[cfg(test)]
mod tests;
