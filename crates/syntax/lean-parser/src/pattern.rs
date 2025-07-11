use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse a pattern
    pub fn pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        match self.peek() {
            Some('(') => self.paren_pattern(),
            Some('_') => self.wildcard_pattern(),
            Some(ch) if ch.is_ascii_digit() => self.literal_pattern(),
            Some('"') => self.literal_pattern(),
            Some('\'') => self.literal_pattern(),
            Some(ch) if ch.is_alphabetic() => {
                // Could be constructor or variable pattern
                let ident = self.identifier()?;
                self.skip_whitespace();

                // Check if it's a constructor pattern with arguments
                if self
                    .peek()
                    .is_some_and(|ch| ch.is_alphabetic() || ch == '(' || ch == '_')
                {
                    // Constructor pattern
                    let mut args = vec![ident];
                    while self
                        .peek()
                        .is_some_and(|ch| ch.is_alphabetic() || ch == '(' || ch == '_')
                    {
                        args.push(self.pattern()?);
                        self.skip_whitespace();
                    }

                    let range = self.input().range_from(start);
                    Ok(Syntax::Node(Box::new(SyntaxNode {
                        kind: SyntaxKind::ConstructorPattern,
                        range,
                        children: args.into(),
                    })))
                } else {
                    // Variable pattern
                    Ok(ident)
                }
            }
            _ => Err(ParseError::boxed(
                ParseErrorKind::Expected("pattern".to_string()),
                start,
            )),
        }
    }

    /// Parse wildcard pattern: `_`
    fn wildcard_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('_')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::WildcardPattern,
            range,
            children: smallvec![],
        })))
    }

    /// Parse parenthesized pattern: `(pattern)` or unit pattern `()`
    fn paren_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('(')?;
        self.skip_whitespace();

        // Check for unit pattern ()
        if self.peek() == Some(')') {
            self.advance(); // consume ')'
            let range = self.input().range_from(start);

            // Create a proper qualified identifier node for Unit.unit
            let unit_atom = Syntax::Atom(lean_syn_expr::SyntaxAtom {
                range,
                value: eterned::BaseCoword::new("Unit"),
            });
            let unit_atom2 = Syntax::Atom(lean_syn_expr::SyntaxAtom {
                range,
                value: eterned::BaseCoword::new("unit"),
            });

            return Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::ConstructorPattern,
                range,
                children: vec![Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::App,
                    range,
                    children: vec![unit_atom, unit_atom2].into(),
                }))]
                .into(),
            })));
        }

        let pattern = self.pattern()?;
        self.skip_whitespace();
        self.expect_char(')')?;
        Ok(pattern)
    }

    /// Parse literal pattern: number, string, or char literal
    fn literal_pattern(&mut self) -> ParserResult<Syntax> {
        match self.peek() {
            Some(ch) if ch.is_ascii_digit() => self.number(),
            Some('"') => self.string_literal(),
            Some('\'') => self.char_literal(),
            _ => Err(ParseError::boxed(
                ParseErrorKind::Expected("literal pattern".to_string()),
                self.position(),
            )),
        }
    }

    /// Parse match expression: `match expr with | pat1 => expr1 | pat2 =>
    /// expr2`
    pub fn match_expr(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("match")?;
        self.skip_whitespace();

        // Parse the expression to match on
        let expr = self.term()?;
        self.skip_whitespace();

        self.keyword("with")?;
        self.skip_whitespace();

        // Parse match arms
        let mut arms = Vec::new();

        // First arm might not have a pipe
        if self.peek() != Some('|') {
            arms.push(self.match_arm()?);
        }

        // Remaining arms with pipes
        while self.peek() == Some('|') {
            self.advance(); // consume '|'
            self.skip_whitespace();
            arms.push(self.match_arm()?);
            self.skip_whitespace();
        }

        let range = self.input().range_from(start);
        let mut children = smallvec![expr];
        children.extend(arms);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Match,
            range,
            children,
        })))
    }

    /// Parse a match arm: `pattern => expr`
    fn match_arm(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let pattern = self.pattern()?;
        self.skip_whitespace();

        // Parse arrow
        if self.peek() == Some('=') && self.input().peek_nth(1) == Some('>') {
            self.advance(); // consume '='
            self.advance(); // consume '>'
        } else if self.peek() == Some('⇒') {
            self.advance();
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("=> or ⇒".to_string()),
                self.position(),
            ));
        }

        self.skip_whitespace();
        let expr = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::MatchArm,
            range,
            children: smallvec![pattern, expr],
        })))
    }
}
