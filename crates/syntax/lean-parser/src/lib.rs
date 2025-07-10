#![feature(if_let_guard)]

pub mod category;
pub mod combinators;
pub mod command;
pub mod custom_syntax;
pub mod diagnostic;
pub mod error;
pub mod expansion;
pub mod input;
pub mod lexical;
pub mod r#macro;
pub mod module;
pub mod parser;
pub mod pattern;
pub mod precedence;
pub mod recovery;
pub mod tactic;
pub mod term;

pub use error::{ParseError, ParseErrorKind};
pub use expansion::ExpandingParser;
pub use input::{Input, ParserInput};
pub use parser::{Parser, ParserResult};

#[cfg(test)]
mod tests;
