#![feature(let_chains)]
#![feature(if_let_guard)]

pub mod input;
pub mod parser;
pub mod combinators;
pub mod error;

pub use input::{Input, ParserInput};
pub use parser::{Parser, ParserResult};
pub use error::{ParseError, ParseErrorKind};

#[cfg(test)]
mod tests;