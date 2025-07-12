//! Advanced implicit argument parsing for Lean 4
//!
//! This module handles parsing of various kinds of implicit arguments:
//! - Implicit arguments: {x : T}
//! - Strict implicit arguments: {{x : T}}
//! - Instance implicit arguments: [inst : TC]
//! - Auto-implicit arguments

use lean_syn_expr::{Syntax, SyntaxAtom, SyntaxKind, SyntaxNode};
use smallvec::SmallVec;

use crate::{
    error::{ParseError, ParseErrorKind},
    lexical::is_id_start,
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse binder: (x : T), {x : T}, {{x : T}}, [x : T], or just x
    pub fn parse_binder(&mut self) -> ParserResult<Syntax> {
        let _start = self.position();

        match self.peek() {
            Some('(') => self.explicit_binder(),
            Some('{') => {
                // Check for strict implicit {{
                if self.input().peek_nth(1) == Some('{') {
                    self.strict_implicit_binder()
                } else {
                    self.implicit_binder()
                }
            }
            Some('[') => self.inst_implicit_binder(),
            Some(c) if is_id_start(c) => {
                // Simple name without type annotation
                self.identifier()
            }
            _ => Err(ParseError::boxed(
                ParseErrorKind::Expected("binder".to_string()),
                self.position(),
            )),
        }
    }

    /// Parse explicit binder: (x : T) or (x y : T)
    fn explicit_binder(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('(')?;
        self.skip_whitespace();

        let mut names = Vec::new();

        // Parse names
        while self.peek().is_some_and(is_id_start) {
            names.push(self.identifier()?);
            self.skip_whitespace();
        }

        if names.is_empty() {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("binder name".to_string()),
                self.position(),
            ));
        }

        // Parse type annotation if present
        let ty = if self.peek() == Some(':') {
            self.advance();
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        self.skip_whitespace();
        self.expect_char(')')?;

        let range = self.input().range_from(start);
        let mut children: SmallVec<[Syntax; 4]> = names.into();
        if let Some(t) = ty {
            children.push(t);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::LeftParen, // Using LeftParen for explicit binder
            range,
            children,
        ))))
    }

    /// Parse implicit binder: {x : T} or {x y : T}
    fn implicit_binder(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('{')?;
        self.skip_whitespace();

        let mut names = Vec::new();

        // Parse names
        while self.peek().is_some_and(is_id_start) {
            names.push(self.identifier()?);
            self.skip_whitespace();
        }

        if names.is_empty() {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("binder name".to_string()),
                self.position(),
            ));
        }

        // Parse type annotation if present
        let ty = if self.peek() == Some(':') {
            self.advance();
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        self.skip_whitespace();
        self.expect_char('}')?;

        let range = self.input().range_from(start);
        let mut children: SmallVec<[Syntax; 4]> = names.into();
        if let Some(t) = ty {
            children.push(t);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::LeftBrace, // Using LeftBrace for implicit binder
            range,
            children,
        ))))
    }

    /// Parse strict implicit binder: {{x : T}}
    fn strict_implicit_binder(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('{')?;
        self.expect_char('{')?;
        self.skip_whitespace();

        let mut names = Vec::new();

        // Parse names
        while self.peek().is_some_and(is_id_start) {
            names.push(self.identifier()?);
            self.skip_whitespace();
        }

        if names.is_empty() {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("binder name".to_string()),
                self.position(),
            ));
        }

        // Type annotation is required for strict implicits
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.term()?;

        self.skip_whitespace();
        self.expect_char('}')?;
        self.expect_char('}')?;

        let range = self.input().range_from(start);
        let mut children: SmallVec<[Syntax; 4]> = names.into();
        children.push(ty);

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::LeftBrace, // TODO: Add proper StrictImplicitBinder kind
            range,
            children,
        ))))
    }

    /// Parse instance implicit binder: [inst : TC]
    fn inst_implicit_binder(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('[')?;
        self.skip_whitespace();

        // Parse optional name
        let has_name = self.peek().is_some_and(is_id_start) && {
            // Look ahead to see if there's a colon after the identifier
            self.input_mut().save_position();
            self.identifier().ok();
            self.skip_whitespace();
            let has_colon = self.peek() == Some(':');
            self.input_mut().restore_position();
            has_colon
        };

        let name = if has_name {
            Some(self.identifier()?)
        } else {
            None
        };

        self.skip_whitespace();

        // Parse type (required)
        let ty = if name.is_some() {
            self.expect_char(':')?;
            self.skip_whitespace();
            self.term()?
        } else {
            self.term()?
        };

        self.skip_whitespace();
        self.expect_char(']')?;

        let range = self.input().range_from(start);
        let mut children = SmallVec::new();
        if let Some(n) = name {
            children.push(n);
        }
        children.push(ty);

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::LeftBracket, // Using LeftBracket for instance implicit
            range,
            children,
        ))))
    }

    /// Parse auto-implicit underscore
    pub fn parse_auto_implicit(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('_')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Atom(SyntaxAtom::new(
            range,
            eterned::BaseCoword::new("_"),
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_binder(input: &str) -> ParserResult<Syntax> {
        let mut parser = Parser::new(input);
        parser.parse_binder()
    }

    #[test]
    fn test_explicit_binder() {
        let result = parse_binder("(x : Nat)").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_implicit_binder() {
        let result = parse_binder("{α : Type}").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_strict_implicit_binder() {
        let result = parse_binder("{{x : Nat}}").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_inst_implicit_binder() {
        let result = parse_binder("[Monad m]").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_inst_implicit_with_name() {
        let result = parse_binder("[inst : Monad m]").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_multiple_names_in_binder() {
        let result = parse_binder("(x y z : Nat)").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }
}
