//! Attribute parsing for Lean 4
//!
//! This module handles parsing of attributes (@[attr], @[attr value], etc.)

use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::{smallvec, SmallVec};

use crate::{
    error::{ParseError, ParseErrorKind},
    lexical::is_id_start,
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse attributes: `@[attr1, attr2 val, attr3]`
    pub fn parse_attribute_list_syntax(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('@')?;
        self.expect_char('[')?;
        self.skip_whitespace();

        let mut attributes = SmallVec::new();

        while self.peek() != Some(']') {
            attributes.push(self.parse_single_attribute()?);
            self.skip_whitespace();

            if self.peek() == Some(',') {
                self.advance();
                self.skip_whitespace();
            } else if self.peek() != Some(']') {
                return Err(ParseError::boxed(
                    ParseErrorKind::Expected(", or ]".to_string()),
                    self.position(),
                ));
            }
        }

        self.expect_char(']')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::AttributeList,
            range,
            children: attributes,
        })))
    }

    /// Parse a single attribute: `attr` or `attr value` or `attr := value`
    fn parse_single_attribute(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let name = self.identifier()?;
        self.skip_whitespace();

        let mut children = smallvec![name];

        // Check for attribute value
        if self.peek() == Some(':') && self.input().peek_nth(1) == Some('=') {
            self.advance(); // :
            self.advance(); // =
            self.skip_whitespace();
            children.push(self.attr_value()?);
        } else if !self.peek_attr_end() {
            // Space-separated value
            children.push(self.attr_value()?);
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Attribute,
            range,
            children,
        })))
    }

    /// Parse attribute value (can be identifier, string, number, or
    /// parenthesized expression)
    fn attr_value(&mut self) -> ParserResult<Syntax> {
        match self.peek() {
            Some('"') => self.string_literal(),
            Some('\'') => self.char_literal(),
            Some(c) if c.is_ascii_digit() => self.number(),
            Some('(') => {
                self.advance(); // (
                self.skip_whitespace();
                let expr = self.term()?;
                self.skip_whitespace();
                self.expect_char(')')?;
                Ok(expr)
            }
            Some(c) if is_id_start(c) => self.identifier(),
            _ => Err(ParseError::boxed(
                ParseErrorKind::Expected("attribute value".to_string()),
                self.position(),
            )),
        }
    }

    /// Check if we're at the end of attribute value parsing
    fn peek_attr_end(&self) -> bool {
        matches!(self.peek(), Some(',') | Some(']') | None)
    }

    /// Parse multiple attributes at once: `@[attr1] @[attr2] ...`
    pub fn parse_attribute_list(&mut self) -> ParserResult<SmallVec<[Syntax; 2]>> {
        let mut attrs = SmallVec::new();

        while self.peek() == Some('@') {
            attrs.push(self.parse_attribute_list_syntax()?);
            self.skip_whitespace();
        }

        Ok(attrs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_attr(input: &str) -> ParserResult<Syntax> {
        let mut parser = Parser::new(input);
        parser.parse_attribute_list_syntax()
    }

    #[test]
    fn test_simple_attribute() {
        let result = parse_attr("@[inline]").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_attribute_with_value() {
        let result = parse_attr("@[simp, inline]").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_attribute_with_assignment() {
        let result = parse_attr("@[priority := 100]").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_multiple_attributes() {
        let result = parse_attr("@[simp, inline, reducible]").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_attribute_with_string_value() {
        let result = parse_attr(r#"@[doc "This is a docstring"]"#).unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_attribute_with_parenthesized_expr() {
        let result = parse_attr("@[priority (10 + 5)]").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }
}
