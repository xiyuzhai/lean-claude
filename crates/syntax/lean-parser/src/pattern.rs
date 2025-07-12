use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse a pattern
    pub fn pattern(&mut self) -> ParserResult<Syntax> {
        self.pattern_with_precedence(crate::precedence::Precedence::MIN)
    }

    /// Parse a pattern with precedence (similar to term parsing)
    fn pattern_with_precedence(
        &mut self,
        min_prec: crate::precedence::Precedence,
    ) -> ParserResult<Syntax> {
        let start = self.position();

        // Parse primary pattern
        let mut left = self.primary_pattern()?;

        // Check for infix operators in patterns
        loop {
            self.skip_whitespace();

            // Check for binary operator
            if let Some(op_info) = self.peek_pattern_operator() {
                if op_info.precedence < min_prec {
                    break;
                }

                let op_str = op_info.symbol.clone();
                let op_prec = op_info.precedence;
                let op_assoc = op_info.associativity;

                // Capture operator position before consuming
                let op_start = self.position();

                // Consume the operator
                for _ in op_str.chars() {
                    self.advance();
                }

                let op_range = self.input().range_from(op_start);

                self.skip_whitespace();

                // Calculate right precedence based on associativity
                let right_prec = match op_assoc {
                    crate::precedence::Associativity::Left => {
                        crate::precedence::Precedence(op_prec.0 + 1)
                    }
                    crate::precedence::Associativity::Right => op_prec,
                    crate::precedence::Associativity::None => {
                        crate::precedence::Precedence(op_prec.0 + 1)
                    }
                };

                // Parse right side
                let right = self.pattern_with_precedence(right_prec)?;

                // Create infix pattern node
                let range = self.input().range_from(start);
                left = Syntax::Node(Box::new(SyntaxNode::new(
                    SyntaxKind::ConstructorPattern, /* Use constructor pattern for infix
                                                     * operators */
                    range,
                    smallvec![
                        Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                            op_range,
                            eterned::BaseCoword::new(op_str),
                        )),
                        left,
                        right
                    ],
                )));
            } else {
                break;
            }
        }

        Ok(left)
    }

    /// Parse primary pattern (no operators)
    fn primary_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        match self.peek() {
            Some('(') => self.paren_pattern(),
            Some('[') => self.list_pattern(),
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
                        args.push(self.primary_pattern()?);
                        self.skip_whitespace();
                    }

                    let range = self.input().range_from(start);
                    Ok(Syntax::Node(Box::new(SyntaxNode::new(
                        SyntaxKind::ConstructorPattern,
                        range,
                        args.into(),
                    ))))
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

    /// Peek multiple characters ahead for pattern parsing
    fn peek_chars_pattern(&self, n: usize) -> String {
        let mut result = String::new();
        for i in 0..n {
            if let Some(ch) = self.input().peek_nth(i) {
                result.push(ch);
            } else {
                break;
            }
        }
        result
    }

    /// Peek at the next operator that could be used in patterns
    fn peek_pattern_operator(&self) -> Option<&'static crate::precedence::OperatorInfo> {
        // For now, only check built-in operators that make sense in patterns
        // In the future, this should also check custom operators registered via
        // notation

        // Try two-character operators first
        let two_char = self.peek_chars_pattern(2);
        if let Some(op_info) = crate::precedence::get_binary_operator(&two_char) {
            // Only allow certain operators in patterns
            if matches!(two_char.as_str(), "::" | "??" | "++" | "<|") {
                return Some(op_info);
            }
        }

        // Then single-character operators
        if let Some(ch) = self.peek() {
            let one_char = ch.to_string();
            if let Some(op_info) = crate::precedence::get_binary_operator(&one_char) {
                // Only allow certain single-char operators in patterns
                if matches!(one_char.as_str(), "|" | "&") {
                    return Some(op_info);
                }
            }
        }

        None
    }

    /// Parse wildcard pattern: `_`
    fn wildcard_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('_')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::WildcardPattern,
            range,
            smallvec![],
        ))))
    }

    /// Parse parenthesized pattern: `(pattern)`, unit pattern `()`, or tuple
    /// pattern `(a, b, c)`
    fn paren_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('(')?;
        self.skip_whitespace();

        // Check for unit pattern ()
        if self.peek() == Some(')') {
            self.advance(); // consume ')'
            let range = self.input().range_from(start);

            // Create a proper qualified identifier node for Unit.unit
            let unit_atom = Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                range,
                eterned::BaseCoword::new("Unit"),
            ));
            let unit_atom2 = Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                range,
                eterned::BaseCoword::new("unit"),
            ));

            return Ok(Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::ConstructorPattern,
                range,
                vec![Syntax::Node(Box::new(SyntaxNode::new(
                    SyntaxKind::App,
                    range,
                    vec![unit_atom, unit_atom2].into(),
                )))]
                .into(),
            ))));
        }

        // Parse first pattern
        let first_pattern = self.pattern()?;
        self.skip_whitespace();

        // Check if this is a tuple pattern (has comma)
        if self.peek() == Some(',') {
            let mut elements = vec![first_pattern];

            while self.peek() == Some(',') {
                self.advance(); // consume ','
                self.skip_whitespace();

                // Allow trailing comma
                if self.peek() == Some(')') {
                    break;
                }

                elements.push(self.pattern()?);
                self.skip_whitespace();
            }

            self.expect_char(')')?;
            let range = self.input().range_from(start);

            // Create tuple pattern
            return Ok(Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::TuplePattern,
                range,
                elements.into(),
            ))));
        }

        // Single parenthesized pattern
        self.expect_char(')')?;
        Ok(first_pattern)
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

    /// Parse list pattern: `[]` or `[x, y, z]`
    fn list_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('[')?;
        self.skip_whitespace();

        let mut elements = Vec::new();

        // Check for empty list
        if self.peek() == Some(']') {
            self.advance(); // consume ']'
            let range = self.input().range_from(start);

            // Empty list is represented as a constructor pattern with "List.nil" or just
            // "[]"
            return Ok(Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::ConstructorPattern,
                range,
                vec![Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                    range,
                    eterned::BaseCoword::new("[]"),
                ))]
                .into(),
            ))));
        }

        // Parse elements
        loop {
            elements.push(self.pattern()?);
            self.skip_whitespace();

            if self.peek() == Some(',') {
                self.advance(); // consume ','
                self.skip_whitespace();
            } else if self.peek() == Some(']') {
                break;
            } else {
                return Err(ParseError::boxed(
                    ParseErrorKind::Expected(", or ]".to_string()),
                    self.position(),
                ));
            }
        }

        self.expect_char(']')?;
        let range = self.input().range_from(start);

        // List patterns become constructor patterns
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::ConstructorPattern,
            range,
            elements.into(),
        ))))
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

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Match,
            range,
            children,
        ))))
    }

    /// Parse a match arm: `pattern => expr` or `pattern if condition => expr`
    fn match_arm(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let pattern = self.pattern()?;
        self.skip_whitespace();

        // Check for guard condition (if clause)
        let mut children = smallvec![pattern];

        if self.peek_keyword("if") {
            self.keyword("if")?;
            self.skip_whitespace();
            let guard_condition = self.term()?;
            children.push(guard_condition);
            self.skip_whitespace();
        }

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
        children.push(expr);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::MatchArm,
            range,
            children,
        ))))
    }
}
