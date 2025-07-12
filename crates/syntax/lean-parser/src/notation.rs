//! Notation parsing for Lean 4
//!
//! This module handles parsing of custom notation definitions,
//! precedence declarations, and operator syntax.

use lean_syn_expr::{Syntax, SyntaxAtom, SyntaxKind, SyntaxNode};
use smallvec::{smallvec, SmallVec};

use crate::{
    error::{ParseError, ParseErrorKind},
    lexical::is_id_start,
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse notation command: `notation "x + y" => x.add y`
    pub fn notation_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("notation")?;
        self.skip_whitespace();

        let mut children = SmallVec::new();

        // Parse optional precedence
        if self.peek_keyword("infix") || self.peek_keyword("prefix") || self.peek_keyword("postfix")
        {
            children.push(self.notation_fixity()?);
            self.skip_whitespace();
        }

        // Parse optional precedence number
        if self.peek() == Some(':') {
            self.advance();
            self.skip_whitespace();
            children.push(self.precedence_spec()?);
            self.skip_whitespace();
        }

        // Parse notation pattern (in quotes)
        if self.peek() == Some('"') {
            children.push(self.string_literal()?);
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("notation pattern in quotes".to_string()),
                self.position(),
            ));
        }

        self.skip_whitespace();
        self.expect_char('=')?;
        self.expect_char('>')?;
        self.skip_whitespace();

        // Parse expansion (what the notation expands to)
        children.push(self.term()?);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::NotationDef,
            range,
            children,
        ))))
    }

    /// Parse notation fixity: `infix`, `prefix`, `postfix`
    fn notation_fixity(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let fixity = if self.peek_keyword("infix") {
            self.keyword("infix")?;
            "infix"
        } else if self.peek_keyword("prefix") {
            self.keyword("prefix")?;
            "prefix"
        } else if self.peek_keyword("postfix") {
            self.keyword("postfix")?;
            "postfix"
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("fixity (infix/prefix/postfix)".to_string()),
                self.position(),
            ));
        };

        let range = self.input().range_from(start);
        Ok(Syntax::Atom(SyntaxAtom::new(
            range,
            eterned::BaseCoword::new(fixity),
        )))
    }

    /// Parse precedence specification: `50` or `max` or `min`
    pub fn precedence_spec(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let prec = if self.peek_keyword("max") {
            self.keyword("max")?;
            "max"
        } else if self.peek_keyword("min") {
            self.keyword("min")?;
            "min"
        } else if let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                let num = self.number()?;
                return Ok(num);
            } else {
                return Err(ParseError::boxed(
                    ParseErrorKind::Expected("precedence value".to_string()),
                    self.position(),
                ));
            }
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("precedence value".to_string()),
                self.position(),
            ));
        };

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Precedence,
            range,
            smallvec![Syntax::Atom(SyntaxAtom::new(
                range,
                eterned::BaseCoword::new(prec),
            ))],
        ))))
    }

    /// Parse infix notation: `infix:50 " + " => HAdd.hAdd`
    pub fn infix_notation(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("infix")?;
        self.skip_whitespace();

        let mut children = SmallVec::new();

        // Parse precedence
        if self.peek() == Some(':') {
            self.advance();
            children.push(self.precedence_spec()?);
            self.skip_whitespace();
        }

        // Parse operator pattern
        children.push(self.string_literal()?);
        self.skip_whitespace();

        self.expect_char('=')?;
        self.expect_char('>')?;
        self.skip_whitespace();

        // Parse expansion
        children.push(self.term()?);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::NotationDef,
            range,
            children,
        ))))
    }

    /// Parse prefix notation: `prefix:75 "-" => Neg.neg`
    pub fn prefix_notation(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("prefix")?;
        self.skip_whitespace();

        let mut children = SmallVec::new();

        // Parse precedence
        if self.peek() == Some(':') {
            self.advance();
            children.push(self.precedence_spec()?);
            self.skip_whitespace();
        }

        // Parse operator pattern
        children.push(self.string_literal()?);
        self.skip_whitespace();

        self.expect_char('=')?;
        self.expect_char('>')?;
        self.skip_whitespace();

        // Parse expansion
        children.push(self.term()?);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::NotationDef,
            range,
            children,
        ))))
    }

    /// Parse postfix notation: `postfix:80 "!" => factorial`
    pub fn postfix_notation(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("postfix")?;
        self.skip_whitespace();

        let mut children = SmallVec::new();

        // Parse precedence
        if self.peek() == Some(':') {
            self.advance();
            children.push(self.precedence_spec()?);
            self.skip_whitespace();
        }

        // Parse operator pattern
        children.push(self.string_literal()?);
        self.skip_whitespace();

        self.expect_char('=')?;
        self.expect_char('>')?;
        self.skip_whitespace();

        // Parse expansion
        children.push(self.term()?);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::NotationDef,
            range,
            children,
        ))))
    }

    /// Parse mixfix notation with parameters
    pub fn mixfix_notation(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("notation")?;
        self.skip_whitespace();

        let mut children = SmallVec::new();

        // Parse precedence if present
        if self.peek() == Some(':') {
            self.advance();
            children.push(self.precedence_spec()?);
            self.skip_whitespace();
        }

        // Parse notation pieces and parameters
        while !self.peek_keyword("=>") && self.peek().is_some() {
            if self.peek() == Some('"') {
                // String literal part of notation
                children.push(self.string_literal()?);
            } else if self.peek().is_some_and(is_id_start) {
                // Parameter identifier
                children.push(self.identifier()?);
            } else {
                break;
            }
            self.skip_whitespace();
        }

        self.expect_char('=')?;
        self.expect_char('>')?;
        self.skip_whitespace();

        // Parse expansion
        children.push(self.term()?);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::NotationDef,
            range,
            children,
        ))))
    }

    /// Parse operator declaration with associativity
    pub fn operator_with_assoc(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let fixity = if self.peek_keyword("infixl") {
            self.keyword("infixl")?;
            "infixl"
        } else if self.peek_keyword("infixr") {
            self.keyword("infixr")?;
            "infixr"
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("infixl or infixr".to_string()),
                self.position(),
            ));
        };

        self.skip_whitespace();

        let mut children = smallvec![Syntax::Atom(SyntaxAtom::new(
            self.input().range_from(start),
            eterned::BaseCoword::new(fixity),
        ))];

        // Parse precedence
        if self.peek() == Some(':') {
            self.advance();
            children.push(self.precedence_spec()?);
            self.skip_whitespace();
        }

        // Parse operator pattern
        children.push(self.string_literal()?);
        self.skip_whitespace();

        self.expect_char('=')?;
        self.expect_char('>')?;
        self.skip_whitespace();

        // Parse expansion
        children.push(self.term()?);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::NotationDef,
            range,
            children,
        ))))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_notation(input: &str) -> ParserResult<Syntax> {
        let mut parser = Parser::new(input);
        parser.notation_command()
    }

    #[test]
    fn test_simple_notation() {
        let result = parse_notation(r#"notation "x + y" => x.add y"#).unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_infix_with_precedence() {
        let result = parse_notation(r#"notation infix:50 "+" => HAdd.hAdd"#).unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_prefix_notation() {
        let result = parse_notation(r#"notation prefix:75 "-" => Neg.neg"#).unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_postfix_notation() {
        let result = parse_notation(r#"notation postfix:80 "!" => factorial"#).unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }
}
