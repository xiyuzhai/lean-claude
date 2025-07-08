#![feature(let_chains)]
#![feature(if_let_guard)]

pub mod input;
pub mod error;
pub mod parser;
pub mod combinators;
pub mod term;
pub mod command;
pub mod module;

pub use input::{Input, ParserInput};
pub use parser::{Parser, ParserResult};
pub use error::{ParseError, ParseErrorKind};

#[cfg(test)]
mod tests;