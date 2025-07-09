use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    lexical::is_id_start,
    parser::{Parser, ParserResult, ParsingMode},
    precedence::{get_binary_operator, get_unary_operator, Associativity, Precedence},
};

impl<'a> Parser<'a> {
    /// Parse a term (expression)
    pub fn term(&mut self) -> ParserResult<Syntax> {
        self.term_with_precedence(Precedence::MIN)
    }

    /// Parse a term with precedence (Pratt parsing)
    pub fn term_with_precedence(&mut self, min_prec: Precedence) -> ParserResult<Syntax> {
        let start = self.position();

        // Parse prefix operator or primary expression
        let mut left = self.prefix_term()?;

        loop {
            self.skip_whitespace();

            // Check for binary operator
            if let Some(op_info) = self.peek_binary_operator() {
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
                    Associativity::Left => Precedence(op_prec.0 + 1),
                    Associativity::Right => op_prec,
                    Associativity::None => Precedence(op_prec.0 + 1),
                };

                // Parse right side
                let right = self.term_with_precedence(right_prec)?;

                // Create binary operation node
                let range = self.input().range_from(start);
                left = Syntax::Node(Box::new(SyntaxNode {
                    kind: match op_str.as_str() {
                        "->" | "→" => SyntaxKind::Arrow,
                        _ => SyntaxKind::BinOp,
                    },
                    range,
                    children: smallvec![
                        left,
                        Syntax::Atom(lean_syn_expr::SyntaxAtom {
                            range: op_range,
                            value: eterned::BaseCoword::new(op_str),
                        }),
                        right
                    ],
                }));
            } else {
                break;
            }
        }

        Ok(left)
    }

    /// Parse prefix term (unary operators or primary)
    fn prefix_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Check for unary operator
        if let Some(op_info) = self.peek_unary_operator() {
            let op_str = op_info.symbol.clone();

            let op_start = self.position();

            // Consume the operator
            for _ in op_str.chars() {
                self.advance();
            }

            let op_range = self.input().range_from(op_start);

            self.skip_whitespace();

            // Parse the operand
            let operand = self.prefix_term()?;

            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::UnaryOp,
                range,
                children: smallvec![
                    Syntax::Atom(lean_syn_expr::SyntaxAtom {
                        range: op_range,
                        value: eterned::BaseCoword::new(op_str),
                    }),
                    operand
                ],
            })))
        } else {
            // Parse primary expression then check for application
            self.app_term()
        }
    }

    /// Peek at the next binary operator
    fn peek_binary_operator(&self) -> Option<&'static crate::precedence::OperatorInfo> {
        // In tactic mode, don't treat <|> as a binary operator
        if self.mode() == ParsingMode::Tactic
            && self.peek() == Some('<')
            && self.input().peek_nth(1) == Some('|')
            && self.input().peek_nth(2) == Some('>')
        {
            return None;
        }

        // Try two-character operators first
        let two_char = self.peek_chars(2);
        if let Some(op_info) = get_binary_operator(&two_char) {
            return Some(op_info);
        }

        // Then single-character operators
        if let Some(ch) = self.peek() {
            let one_char = ch.to_string();
            if let Some(op_info) = get_binary_operator(&one_char) {
                return Some(op_info);
            }
        }

        None
    }

    /// Peek at the next unary operator
    fn peek_unary_operator(&self) -> Option<&'static crate::precedence::OperatorInfo> {
        if let Some(ch) = self.peek() {
            let one_char = ch.to_string();
            if let Some(op_info) = get_unary_operator(&one_char) {
                return Some(op_info);
            }
        }
        None
    }

    /// Peek multiple characters ahead
    fn peek_chars(&self, n: usize) -> String {
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

    /// Parse application: `f x y z`
    pub fn app_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut terms = vec![self.atom_term()?];

        loop {
            self.skip_whitespace();

            // Stop at keywords that shouldn't be consumed as arguments
            if self.peek_keyword("with")
                || self.peek_keyword("then")
                || self.peek_keyword("else")
                || self.peek_keyword("in")
                || self.peek_keyword("from")
                // Stop at command keywords
                || self.peek_keyword("def")
                || self.peek_keyword("theorem")
                || self.peek_keyword("axiom")
                || self.peek_keyword("constant")
                || self.peek_keyword("variable")
                || self.peek_keyword("instance")
                || self.peek_keyword("class")
                || self.peek_keyword("structure")
                || self.peek_keyword("inductive")
                || self.peek_keyword("import")
                || self.peek_keyword("namespace")
                || self.peek_keyword("section")
                || self.peek_keyword("end")
                || self.peek_keyword("open")
                || self.peek_keyword("universe")
            {
                break;
            }

            // Check if we can parse another atom
            if let Ok(arg) = self.try_parse(|p| p.atom_term()) {
                terms.push(arg);
            } else {
                break;
            }
        }

        if terms.len() == 1 {
            Ok(terms.into_iter().next().unwrap())
        } else {
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::App,
                range,
                children: terms.into(),
            })))
        }
    }

    /// Parse atomic term
    pub fn atom_term(&mut self) -> ParserResult<Syntax> {
        self.skip_whitespace();

        match self.peek() {
            Some('(') => self.paren_term(),
            Some('{') => self.implicit_term(),
            Some('[') => self.inst_implicit_term(),
            Some('λ') | Some('\\') => self.lambda_term(),
            Some('∀') => self.forall_term(),
            Some('l') if self.peek_keyword("let") => self.let_term(),
            Some('h') if self.peek_keyword("have") => self.have_term(),
            Some('s') if self.peek_keyword("show") => self.show_term(),
            Some('f') if self.peek_keyword("fun") => self.lambda_term(),
            Some('f') if self.peek_keyword("forall") => self.forall_term(),
            Some('m') if self.peek_keyword("match") => self.match_expr(),
            Some('i') if self.peek_keyword("if") => self.if_term(),
            Some('b') if self.peek_keyword("by") => self.by_tactic(),
            Some('`') if self.input().peek_nth(1) == Some('(') => self.parse_syntax_quotation(),
            Some('r') if self.peek_raw_string() => self.raw_string_literal(),
            Some('s') if self.peek_interpolated_string() => self.interpolated_string_literal(),
            Some('0') if self.peek_special_number() => self.number(),
            Some(ch) if ch.is_ascii_digit() => self.number(),
            Some('"') => self.string_literal(),
            Some('\'') => self.char_literal(),
            Some(ch) if is_id_start(ch) => self.identifier(),
            Some(_) => Err(ParseError::boxed(
                ParseErrorKind::Expected("term".to_string()),
                self.position(),
            )),
            None => Err(ParseError::boxed(
                ParseErrorKind::UnexpectedEof,
                self.position(),
            )),
        }
    }

    /// Parse parenthesized term: `(term)`
    pub fn paren_term(&mut self) -> ParserResult<Syntax> {
        self.expect_char('(')?;
        self.skip_whitespace();
        let term = self.term()?;
        self.skip_whitespace();
        self.expect_char(')')?;
        Ok(term)
    }

    /// Parse implicit term: `{term}` or implicit binder `{x : Type}`
    pub fn implicit_term(&mut self) -> ParserResult<Syntax> {
        // This is actually parsing a binder group in implicit braces
        // It's already handled by binder_group(), so just delegate to it
        self.binder_group()
    }

    /// Parse instance implicit term: `[term]` or instance implicit binder
    /// `[Monad m]`
    pub fn inst_implicit_term(&mut self) -> ParserResult<Syntax> {
        // This is actually parsing a binder group in instance implicit brackets
        // It's already handled by binder_group(), so just delegate to it
        self.binder_group()
    }

    /// Parse if-then-else expression
    pub fn if_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("if")?;
        self.skip_whitespace();

        let cond = self.term()?;
        self.skip_whitespace();

        self.keyword("then")?;
        self.skip_whitespace();

        let then_branch = self.term()?;
        self.skip_whitespace();

        self.keyword("else")?;
        self.skip_whitespace();

        let else_branch = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Match, // Reuse Match for if-then-else for now
            range,
            children: smallvec![cond, then_branch, else_branch],
        })))
    }

    /// Parse lambda: `λ x => body` or `fun x => body`
    pub fn lambda_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Consume lambda symbol
        if self.peek() == Some('λ') || self.peek() == Some('\\') {
            self.advance();
        } else {
            self.keyword("fun")?;
        }

        self.skip_whitespace();

        // Parse binders
        let mut binders = Vec::new();
        while self.peek() != Some('=') && self.peek() != Some('→') {
            if self.peek() == Some('{') || self.peek() == Some('[') || self.peek() == Some('(') {
                binders.push(self.binder_group()?);
            } else if self.peek().is_some_and(is_id_start) {
                binders.push(self.identifier()?);
            } else {
                break;
            }
            self.skip_whitespace();
        }

        // Parse arrow
        if self.peek() == Some('=') && self.input().peek_nth(1) == Some('>') {
            self.advance(); // consume '='
            self.advance(); // consume '>'
        } else if self.peek() == Some('→') {
            self.advance();
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("=> or →".to_string()),
                self.position(),
            ));
        }

        self.skip_whitespace();
        let body = self.term()?;

        let range = self.input().range_from(start);
        let mut children = binders;
        children.push(body);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Lambda,
            range,
            children: children.into(),
        })))
    }

    /// Parse forall: `∀ x, P x` or `forall x, P x`
    pub fn forall_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Consume forall symbol
        if self.peek() == Some('∀') {
            self.advance();
        } else {
            self.keyword("forall")?;
        }

        self.skip_whitespace();

        // Parse binders
        let mut binders = Vec::new();
        while self.peek() != Some(',') {
            if self.peek() == Some('{') || self.peek() == Some('[') || self.peek() == Some('(') {
                binders.push(self.binder_group()?);
            } else if self.peek().is_some_and(is_id_start) {
                binders.push(self.identifier()?);
            } else {
                break;
            }
            self.skip_whitespace();
        }

        // Parse comma
        self.expect_char(',')?;
        self.skip_whitespace();

        let body = self.term()?;

        let range = self.input().range_from(start);
        let mut children = binders;
        children.push(body);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Forall,
            range,
            children: children.into(),
        })))
    }

    /// Parse let: `let x := e in body`
    pub fn let_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("let")?;
        self.skip_whitespace();

        let name = self.identifier()?;
        self.skip_whitespace();

        // Optional type annotation
        let ty = if self.peek() == Some(':') && self.input().peek_nth(1) != Some('=') {
            self.advance();
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        self.skip_whitespace();
        self.expect_char(':')?;
        self.expect_char('=')?;
        self.skip_whitespace();

        let value = self.term()?;
        self.skip_whitespace();

        // Optional 'in'
        if self.peek_keyword("in") {
            self.keyword("in")?;
            self.skip_whitespace();
        }

        let body = self.term()?;

        let range = self.input().range_from(start);
        let mut children = smallvec![name];
        if let Some(t) = ty {
            children.push(t);
        }
        children.push(value);
        children.push(body);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Let,
            range,
            children,
        })))
    }

    /// Parse have: `have h : P := proof`
    pub fn have_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("have")?;
        self.skip_whitespace();

        let name = self.identifier()?;
        self.skip_whitespace();

        self.expect_char(':')?;
        self.skip_whitespace();

        let ty = self.term()?;
        self.skip_whitespace();

        self.expect_char(':')?;
        self.expect_char('=')?;
        self.skip_whitespace();

        let proof = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Have,
            range,
            children: smallvec![name, ty, proof],
        })))
    }

    /// Parse show: `show P from proof`
    pub fn show_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("show")?;
        self.skip_whitespace();

        let ty = self.term()?;
        self.skip_whitespace();

        self.keyword("from")?;
        self.skip_whitespace();

        let proof = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Show,
            range,
            children: smallvec![ty, proof],
        })))
    }
}
