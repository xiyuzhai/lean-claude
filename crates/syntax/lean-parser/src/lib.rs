#![feature(if_let_guard)]

pub mod combinators;
pub mod command;
pub mod error;
pub mod input;
pub mod module;
pub mod parser;
pub mod pattern;
pub mod precedence;
pub mod term;

pub use error::{ParseError, ParseErrorKind};
pub use input::{Input, ParserInput};
pub use parser::{Parser, ParserResult};

#[cfg(test)]
mod tests;
