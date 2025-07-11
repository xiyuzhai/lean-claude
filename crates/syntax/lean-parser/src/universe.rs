//! Universe level parsing for Lean 4
//!
//! This module handles parsing of universe levels and universe polymorphism

use lean_syn_expr::{Syntax, SyntaxAtom, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    lexical::is_id_start,
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse universe level: `u`, `u+1`, `max u v`, etc.
    pub fn universe_level(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Try to parse imax first since it starts with a keyword
        if self.peek_keyword("imax") {
            return self.imax_level();
        }

        // Try to parse max
        if self.peek_keyword("max") {
            return self.max_level();
        }

        // Parse atomic level then check for successor
        let base = self.atomic_universe_level()?;

        // Check for successor notation
        self.skip_whitespace();
        if self.peek() == Some('+') {
            self.advance();
            self.skip_whitespace();

            // Must be followed by a number
            if let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    let num = self.number()?;
                    let range = self.input().range_from(start);
                    return Ok(Syntax::Node(Box::new(SyntaxNode {
                        kind: SyntaxKind::UniverseSucc,
                        range,
                        children: smallvec![base, num],
                    })));
                }
            }

            return Err(ParseError::boxed(
                ParseErrorKind::Expected("number after + in universe level".to_string()),
                self.position(),
            ));
        }

        Ok(base)
    }

    /// Parse atomic universe level: identifier, number, or parenthesized level
    fn atomic_universe_level(&mut self) -> ParserResult<Syntax> {
        match self.peek() {
            Some('(') => {
                self.advance();
                self.skip_whitespace();
                let level = self.universe_level()?;
                self.skip_whitespace();
                self.expect_char(')')?;
                Ok(level)
            }
            Some(c) if c.is_ascii_digit() => {
                // Universe literal (0, 1, 2, etc.)
                self.number()
            }
            Some(c) if is_id_start(c) => {
                // Universe variable
                self.identifier()
            }
            _ => Err(ParseError::boxed(
                ParseErrorKind::Expected("universe level".to_string()),
                self.position(),
            )),
        }
    }

    /// Parse max level: `max u v`
    fn max_level(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("max")?;
        self.skip_whitespace();

        let level1 = self.universe_level()?;
        self.skip_whitespace();
        let level2 = self.universe_level()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::UniverseMax,
            range,
            children: smallvec![level1, level2],
        })))
    }

    /// Parse imax level: `imax u v`
    fn imax_level(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("imax")?;
        self.skip_whitespace();

        let level1 = self.universe_level()?;
        self.skip_whitespace();
        let level2 = self.universe_level()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::UniverseIMax,
            range,
            children: smallvec![level1, level2],
        })))
    }

    /// Parse universe declaration: `universe u v w`
    pub fn parse_universe_declaration(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("universe")?;
        self.skip_whitespace();

        let mut names = Vec::new();

        // Parse universe variable names
        while self.peek().is_some_and(is_id_start) {
            names.push(self.identifier()?);
            self.skip_whitespace();
        }

        if names.is_empty() {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("universe variable name".to_string()),
                self.position(),
            ));
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Universe,
            range,
            children: names.into(),
        })))
    }

    /// Parse Sort or Type with universe level
    pub fn sort_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        if self.peek_keyword("Sort") {
            self.keyword("Sort")?;
            self.skip_whitespace();

            // Sort can be followed by a universe level or *
            if self.peek() == Some('*') {
                self.advance();
                let range = self.input().range_from(start);
                return Ok(Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::Sort,
                    range,
                    children: smallvec![Syntax::Atom(SyntaxAtom {
                        range,
                        value: eterned::BaseCoword::new("*"),
                    })],
                })));
            } else if self.peek().is_some() && !self.peek_term_end() {
                let level = self.universe_level()?;
                let range = self.input().range_from(start);
                return Ok(Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::Sort,
                    range,
                    children: smallvec![level],
                })));
            } else {
                // Just Sort without level
                let range = self.input().range_from(start);
                return Ok(Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::Sort,
                    range,
                    children: smallvec![],
                })));
            }
        }

        if self.peek_keyword("Type") {
            self.keyword("Type")?;
            self.skip_whitespace();

            // Type can be followed by a universe level or *
            if self.peek() == Some('*') {
                self.advance();
                let range = self.input().range_from(start);
                return Ok(Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::Type,
                    range,
                    children: smallvec![Syntax::Atom(SyntaxAtom {
                        range,
                        value: eterned::BaseCoword::new("*"),
                    })],
                })));
            } else if self.peek().is_some() && !self.peek_term_end() {
                let level = self.universe_level()?;
                let range = self.input().range_from(start);
                return Ok(Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::Type,
                    range,
                    children: smallvec![level],
                })));
            } else {
                // Just Type without level (Type 0)
                let range = self.input().range_from(start);
                return Ok(Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::Type,
                    range,
                    children: smallvec![],
                })));
            }
        }

        if self.peek_keyword("Prop") {
            self.keyword("Prop")?;
            let range = self.input().range_from(start);
            return Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::Prop,
                range,
                children: smallvec![],
            })));
        }

        Err(ParseError::boxed(
            ParseErrorKind::Expected("Sort, Type, or Prop".to_string()),
            self.position(),
        ))
    }

    /// Check if we're at a term boundary
    fn peek_term_end(&self) -> bool {
        match self.peek() {
            None => true,
            Some(c) => match c {
                ')' | ']' | '}' | ',' | ';' | ':' => true,
                '=' if self.input().peek_nth(1) == Some('>') => true,
                '→' => true,
                _ => false,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_universe(input: &str) -> ParserResult<Syntax> {
        let mut parser = Parser::new(input);
        parser.universe_level()
    }

    fn parse_sort(input: &str) -> ParserResult<Syntax> {
        let mut parser = Parser::new(input);
        parser.sort_term()
    }

    #[test]
    fn test_simple_universe() {
        let result = parse_universe("u").unwrap();
        assert!(matches!(result, Syntax::Atom(_)));
    }

    #[test]
    fn test_universe_successor() {
        let result = parse_universe("u+1").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_universe_max() {
        let result = parse_universe("max u v").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_universe_imax() {
        let result = parse_universe("imax u v").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_complex_universe() {
        let result = parse_universe("max (u+1) (imax v w)").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_sort_with_level() {
        let result = parse_sort("Sort u").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_type_star() {
        let result = parse_sort("Type*").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }

    #[test]
    fn test_prop() {
        let result = parse_sort("Prop").unwrap();
        assert!(matches!(result, Syntax::Node(_)));
    }
}
