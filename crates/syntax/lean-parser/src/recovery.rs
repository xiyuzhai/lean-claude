//! Error recovery mechanisms for the Lean parser
//!
//! This module provides strategies for recovering from parse errors to continue
//! parsing and provide better error messages.

use lean_syn_expr::{SourceRange, Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserResult},
};

/// Recovery strategies for different contexts
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryStrategy {
    /// Skip to next statement/command
    SkipToNextStatement,
    /// Skip to matching delimiter
    SkipToDelimiter(char),
    /// Skip to one of several tokens
    SkipToTokens(&'static [&'static str]),
    /// Insert missing token and continue
    InsertToken(&'static str),
    /// Try alternative parse
    TryAlternative,
}

impl<'a> Parser<'a> {
    /// Attempt to recover from a parse error
    pub fn recover_from_error(
        &mut self,
        error: Box<ParseError>,
        strategy: RecoveryStrategy,
    ) -> ParserResult<Syntax> {
        // Record the error for later reporting
        self.record_error(error.clone());

        match strategy {
            RecoveryStrategy::SkipToNextStatement => self.skip_to_next_statement(),
            RecoveryStrategy::SkipToDelimiter(delim) => self.skip_to_delimiter(delim),
            RecoveryStrategy::SkipToTokens(tokens) => self.skip_to_tokens(tokens),
            RecoveryStrategy::InsertToken(token) => self.insert_missing_token(token),
            RecoveryStrategy::TryAlternative => self.try_alternative_parse(),
        }
    }

    /// Skip tokens until we find what looks like the start of a new statement
    fn skip_to_next_statement(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut skipped = Vec::new();

        while !self.input().is_at_end() {
            // Check for statement starters
            if self.peek_keyword("def")
                || self.peek_keyword("theorem")
                || self.peek_keyword("instance")
                || self.peek_keyword("inductive")
                || self.peek_keyword("structure")
                || self.peek_keyword("class")
                || self.peek_keyword("axiom")
                || self.peek_keyword("constant")
                || self.peek_keyword("variable")
                || self.peek_keyword("namespace")
                || self.peek_keyword("end")
                || self.peek_keyword("#")
            {
                break;
            }

            // Skip one character
            if let Some(ch) = self.advance() {
                skipped.push(ch);
            }
        }

        // Create an error node containing the skipped content
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Error,
            range,
            children: smallvec![],
        })))
    }

    /// Skip until we find a matching delimiter
    fn skip_to_delimiter(&mut self, target: char) -> ParserResult<Syntax> {
        let start = self.position();
        let mut depth = 1;

        let (open, close) = match target {
            ')' => ('(', ')'),
            ']' => ('[', ']'),
            '}' => ('{', '}'),
            _ => return self.skip_to_next_statement(),
        };

        while !self.input().is_at_end() && depth > 0 {
            match self.peek() {
                Some(ch) if ch == open => {
                    depth += 1;
                    self.advance();
                }
                Some(ch) if ch == close => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                    self.advance();
                }
                _ => {
                    self.advance();
                }
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Error,
            range,
            children: smallvec![],
        })))
    }

    /// Skip until we find one of the specified tokens
    fn skip_to_tokens(&mut self, tokens: &[&str]) -> ParserResult<Syntax> {
        let start = self.position();

        while !self.input().is_at_end() {
            for token in tokens {
                if self.peek_keyword(token) {
                    let range = self.input().range_from(start);
                    return Ok(Syntax::Node(Box::new(SyntaxNode {
                        kind: SyntaxKind::Error,
                        range,
                        children: smallvec![],
                    })));
                }
            }
            self.advance();
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Error,
            range,
            children: smallvec![],
        })))
    }

    /// Insert a missing token and create a synthetic node
    fn insert_missing_token(&mut self, token: &str) -> ParserResult<Syntax> {
        let pos = self.position();
        let range = SourceRange {
            start: pos,
            end: pos,
        };

        // Create a synthetic atom for the missing token
        Ok(Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range,
            value: eterned::BaseCoword::new(token),
        }))
    }

    /// Try an alternative parse when the primary one fails
    fn try_alternative_parse(&mut self) -> ParserResult<Syntax> {
        // This is a placeholder - specific alternatives would be implemented
        // based on context
        self.skip_to_next_statement()
    }

    /// Parse with recovery - try to parse, recover on error
    pub fn parse_with_recovery<F, T>(
        &mut self,
        parser: F,
        recovery: RecoveryStrategy,
    ) -> ParserResult<T>
    where
        F: FnOnce(&mut Self) -> ParserResult<T>,
        T: From<Syntax>,
    {
        match parser(self) {
            Ok(result) => Ok(result),
            Err(error) => {
                let recovered = self.recover_from_error(error, recovery)?;
                Ok(T::from(recovered))
            }
        }
    }

    /// Parse a delimited list with recovery
    pub fn parse_delimited_with_recovery<F, T>(
        &mut self,
        open: char,
        close: char,
        separator: Option<char>,
        mut parser: F,
    ) -> ParserResult<Vec<T>>
    where
        F: FnMut(&mut Self) -> ParserResult<T>,
    {
        self.expect_char(open)?;
        self.skip_whitespace();

        let mut items = Vec::new();

        while self.peek() != Some(close) && !self.input().is_at_end() {
            match parser(self) {
                Ok(item) => items.push(item),
                Err(error) => {
                    self.record_error(error);

                    // Skip to next separator or closing delimiter
                    while !self.input().is_at_end() {
                        match self.peek() {
                            Some(ch) if ch == close => break,
                            Some(ch) if separator.is_some() && ch == separator.unwrap() => {
                                self.advance();
                                self.skip_whitespace();
                                break;
                            }
                            _ => {
                                self.advance();
                            }
                        }
                    }
                }
            }

            self.skip_whitespace();

            if let Some(sep) = separator {
                if self.peek() == Some(sep) {
                    self.advance();
                    self.skip_whitespace();
                } else if self.peek() != Some(close) {
                    // Missing separator - record error but continue
                    let error = ParseError::new(
                        ParseErrorKind::Expected(format!("'{sep}'")),
                        self.position(),
                    );
                    self.record_error(Box::new(error));
                }
            }
        }

        self.expect_char(close)?;
        Ok(items)
    }

    /// Check if we should attempt recovery based on error count
    pub fn should_attempt_recovery(&self) -> bool {
        !self.too_many_errors()
    }

    /// Synchronize to a known good state
    pub fn synchronize(&mut self) {
        // Skip to next likely synchronization point
        while !self.input().is_at_end() {
            if self.peek_keyword("def")
                || self.peek_keyword("theorem")
                || self.peek_keyword("instance")
                || self.peek_keyword("end")
                || self.peek() == Some('\n')
            {
                break;
            }
            self.advance();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_skip_to_delimiter() {
        let input = "foo bar) baz";
        let mut parser = Parser::new(input);

        // Simulate being inside parentheses
        let result = parser.skip_to_delimiter(')');
        assert!(result.is_ok());
        assert_eq!(parser.peek(), Some(')'));
    }

    #[test]
    fn test_skip_to_next_statement() {
        let input = "garbage text def foo := 42";
        let mut parser = Parser::new(input);

        let result = parser.skip_to_next_statement();
        assert!(result.is_ok());
        assert!(parser.peek_keyword("def"));
    }

    #[test]
    fn test_parse_delimited_with_recovery() {
        let input = "[1, bad syntax, 3, 4 oops, 5]";
        let mut parser = Parser::new(input);

        let result = parser.parse_delimited_with_recovery('[', ']', Some(','), |p| p.number());

        assert!(result.is_ok());
        let items = result.unwrap();
        // Should recover and parse at least some numbers
        assert!(!items.is_empty());
    }
}
