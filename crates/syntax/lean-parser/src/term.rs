use eterned::BaseCoword;
use lean_syn_expr::{Syntax, SyntaxAtom, SyntaxKind, SyntaxNode};
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

            // Stop at := which indicates definition/proof
            if self.peek() == Some(':') && self.input().peek_nth(1) == Some('=') {
                break;
            }

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
                left = Syntax::Node(Box::new(SyntaxNode::new(
                    match op_str.as_str() {
                        "->" | "→" => SyntaxKind::Arrow,
                        _ => SyntaxKind::BinOp,
                    },
                    range,
                    smallvec![
                        left,
                        Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                            op_range,
                            eterned::BaseCoword::new(op_str),
                        )),
                        right
                    ],
                )));
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
            Ok(Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::UnaryOp,
                range,
                smallvec![
                    Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                        op_range,
                        eterned::BaseCoword::new(op_str),
                    )),
                    operand
                ],
            ))))
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
        let mut left = self.atom_term()?;

        // Handle projections first (e.g., x.1, x.field)
        left = self.parse_projections(left)?;

        let mut terms = vec![left];

        loop {
            self.skip_whitespace();

            // Stop at keywords that shouldn't be consumed as arguments
            if self.peek_keyword("with")
                || self.peek_keyword("then")
                || self.peek_keyword("else")
                || self.peek_keyword("in")
                || self.peek_keyword("from")
                || self.peek_keyword("deriving")
                // Stop at do-block keywords when in do context
                || self.peek_keyword("return")
                || self.peek_keyword("pure")
                || self.peek_keyword("let")
                || self.peek_keyword("for")
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
                // Stop at := which indicates definition
                || (self.peek() == Some(':') && self.input().peek_nth(1) == Some('='))
            {
                break;
            }

            // Check if we can parse another atom
            if let Ok(arg) = self.try_parse(|p| {
                let atom = p.atom_term()?;
                p.parse_projections(atom)
            }) {
                terms.push(arg);
            } else {
                break;
            }
        }

        if terms.len() == 1 {
            Ok(terms.into_iter().next().unwrap())
        } else {
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::App,
                range,
                terms.into(),
            ))))
        }
    }

    /// Parse atomic term
    pub fn atom_term(&mut self) -> ParserResult<Syntax> {
        self.skip_whitespace();

        match self.peek() {
            Some('(') => self.paren_term(),
            Some('{') => self.implicit_term(),
            Some('[') => self.bracket_term(),
            Some('λ') | Some('\\') => self.lambda_term(),
            Some('∀') => self.forall_term(),
            Some('l') if self.peek_keyword("let") => self.let_term(),
            Some('h') if self.peek_keyword("have") => self.have_term(),
            Some('s') if self.peek_keyword("show") => self.show_term(),
            Some('c') if self.peek_keyword("calc") => self.calc_term(),
            Some('f') if self.peek_keyword("fun") => self.lambda_term(),
            Some('f') if self.peek_keyword("forall") => self.forall_term(),
            Some('S') if self.peek_keyword("Sort") => self.sort_term(),
            Some('T') if self.peek_keyword("Type") => self.sort_term(),
            Some('P') if self.peek_keyword("Prop") => self.sort_term(),
            Some('m') if self.peek_keyword("match") => self.match_expr(),
            Some('i') if self.peek_keyword("if") => self.if_term(),
            Some('b') if self.peek_keyword("by") => self.by_tactic(),
            Some('d') if self.peek_keyword("do") => self.do_term(),
            Some('`') if self.input().peek_nth(1) == Some('(') => self.parse_syntax_quotation(),
            Some('$') => self.parse_antiquotation(),
            Some('⟨') => self.anonymous_constructor(),
            Some('@') => self.explicit_application(),
            Some('·') => self.cdot_placeholder(),
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

    /// Parse parenthesized term: `(term)` or unit `()`
    pub fn paren_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('(')?;
        self.skip_whitespace();

        // Check for unit value ()
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
                SyntaxKind::App,
                range,
                vec![unit_atom, unit_atom2].into(),
            ))));
        }

        let term = self.term()?;
        self.skip_whitespace();
        self.expect_char(')')?;
        Ok(term)
    }

    /// Parse implicit term: `{term}` or implicit binder `{x : Type}` or subtype
    /// `{x : T // P}`
    pub fn implicit_term(&mut self) -> ParserResult<Syntax> {
        let _start = self.position();

        // Try to parse as a subtype expression first
        if let Ok(subtype) = self.try_parse(|p| p.parse_subtype()) {
            return Ok(subtype);
        }

        // Otherwise, parse as a binder group
        self.binder_group()
    }

    /// Parse instance implicit term: `[term]` or instance implicit binder
    /// `[Monad m]`
    pub fn inst_implicit_term(&mut self) -> ParserResult<Syntax> {
        // This is actually parsing a binder group in instance implicit brackets
        // It's already handled by binder_group(), so just delegate to it
        self.binder_group()
    }

    /// Parse bracket term: could be list literal `[a, b, c]` or instance
    /// implicit `[Monad m]`
    pub fn bracket_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('[')?;
        self.skip_whitespace();

        // Empty list
        if self.peek() == Some(']') {
            self.advance(); // consume ']'
            let range = self.input().range_from(start);
            return Ok(Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::List,
                range,
                smallvec![],
            ))));
        }

        // Try to parse as a list literal first
        // We need to look ahead to determine if this is a list or instance implicit
        self.input_mut().save_position();

        // Try parsing as list elements
        let mut elements = Vec::new();
        let mut is_list = true;
        let mut saw_comma = false;

        loop {
            // Try to parse an element
            match self.try_parse(|p| p.term()) {
                Ok(elem) => {
                    // Check if this looks like a type application (e.g., Monad m)
                    // If the first element is an identifier followed by another identifier,
                    // it's likely an instance implicit like [Monad m]
                    if elements.is_empty() && !saw_comma {
                        if let Syntax::Atom(_atom) = &elem {
                            // This is a single identifier
                            self.skip_whitespace();
                            if self.peek().is_some_and(|c| c.is_alphabetic()) {
                                // Followed by another identifier - likely instance implicit
                                is_list = false;
                                break;
                            }
                        }
                    }

                    elements.push(elem);
                    self.skip_whitespace();

                    if self.peek() == Some(',') {
                        // Definitely a list
                        saw_comma = true;
                        self.advance(); // consume ','
                        self.skip_whitespace();
                    } else if self.peek() == Some(']') {
                        // End of bracket expression
                        break;
                    } else {
                        // Not a comma or closing bracket - probably instance implicit
                        is_list = false;
                        break;
                    }
                }
                Err(_) => {
                    is_list = false;
                    break;
                }
            }
        }

        // Only treat as list if we saw a comma OR it's empty OR it's a single element
        // that looks like a literal
        if is_list
            && self.peek() == Some(']')
            && (saw_comma
                || elements.is_empty()
                || (elements.len() == 1
                    && match &elements[0] {
                        // Numbers are parsed as atoms
                        Syntax::Atom(atom) => atom
                            .value
                            .as_str()
                            .chars()
                            .next()
                            .is_some_and(|c| c.is_numeric()),
                        // String literals would be nodes
                        Syntax::Node(node) => matches!(node.kind, SyntaxKind::StringLit),
                        _ => false,
                    }))
        {
            self.advance(); // consume ']'
            self.input_mut().commit_position(); // Commit the saved position
            let range = self.input().range_from(start);
            return Ok(Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::List,
                range,
                elements.into(),
            ))));
        }

        // Not a list, restore and parse as instance implicit
        self.input_mut().restore_position();
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
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Match, // Reuse Match for if-then-else for now
            range,
            smallvec![cond, then_branch, else_branch],
        ))))
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

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Lambda,
            range,
            children.into(),
        ))))
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
        while self.peek() != Some(',') && !self.input().is_at_end() {
            if self.peek() == Some('{') || self.peek() == Some('[') || self.peek() == Some('(') {
                binders.push(self.binder_group()?);
            } else if self.peek().is_some_and(is_id_start) {
                // Try to parse a typed binder without parentheses
                let name = self.identifier()?;
                self.skip_whitespace();

                if self.peek() == Some(':') {
                    // This is a typed binder: x : T
                    self.advance(); // consume ':'
                    self.skip_whitespace();
                    let ty = self.term()?;

                    // Create a binder node
                    let binder_range = self.input().range_from(start);
                    let binder = Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::LeftParen, binder_range, smallvec![name, ty])));
                    binders.push(binder);
                } else {
                    // Just a name
                    binders.push(name);
                }
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

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Forall,
            range,
            children.into(),
        ))))
    }

    /// Parse let: `let x := e in body`
    pub fn let_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("let")?;
        self.skip_whitespace();

        // Check for 'mut' keyword
        let _is_mut = if self.peek_keyword("mut") {
            self.keyword("mut")?;
            self.skip_whitespace();
            true
        } else {
            false
        };

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

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Let,
            range,
            children,
        ))))
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
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Have,
            range,
            smallvec![name, ty, proof],
        ))))
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
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Show,
            range,
            smallvec![ty, proof],
        ))))
    }

    /// Parse calc term: `calc a = b := proof1 _ = c := proof2`
    pub fn calc_term(&mut self) -> ParserResult<Syntax> {
        // Just delegate to the tactic version which has the full implementation
        self.calc_tactic()
    }

    /// Parse subtype expression: `{x : T // P}`
    fn parse_subtype(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('{')?;
        self.skip_whitespace();

        // Parse name
        let name = self.identifier()?;
        self.skip_whitespace();

        self.expect_char(':')?;
        self.skip_whitespace();

        // Parse type - use atom_term to avoid consuming //
        let ty = self.atom_term()?;
        self.skip_whitespace();

        // Check for //
        if self.peek() != Some('/') || self.input().peek_nth(1) != Some('/') {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("//".to_string()),
                self.position(),
            ));
        }
        self.advance(); // consume first /
        self.advance(); // consume second /
        self.skip_whitespace();

        // Parse predicate
        let pred = self.term()?;
        self.skip_whitespace();

        self.expect_char('}')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Subtype,
            range,
            smallvec![name, ty, pred],
        ))))
    }

    /// Parse anonymous constructor: `⟨expr, ...⟩`
    fn anonymous_constructor(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('⟨')?;
        self.skip_whitespace();

        let mut elements = Vec::new();

        // Parse elements
        if self.peek() != Some('⟩') {
            loop {
                elements.push(self.term()?);
                self.skip_whitespace();

                if self.peek() == Some(',') {
                    self.advance();
                    self.skip_whitespace();
                } else {
                    break;
                }
            }
        }

        self.expect_char('⟩')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::AnonymousConstructor,
            range,
            elements.into(),
        ))))
    }

    /// Parse explicit application: `@f arg1 arg2`
    fn explicit_application(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('@')?;
        // No whitespace after @

        let func = self.atom_term()?;
        self.skip_whitespace();

        let mut args = vec![func];

        // Parse arguments
        while !self.at_term_boundary() {
            if let Ok(arg) = self.try_parse(|p| p.atom_term()) {
                args.push(arg);
                self.skip_whitespace();
            } else {
                break;
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::ExplicitApp,
            range,
            args.into(),
        ))))
    }

    /// Check if we're at a term boundary
    fn at_term_boundary(&self) -> bool {
        matches!(
            self.peek(),
            None | Some(',')
                | Some(';')
                | Some(')')
                | Some('}')
                | Some(']')
                | Some('|')
                | Some('⟩')
        )
    }

    /// Parse projections and method calls: x.1, x.field, xs.reverse, list.map f
    fn parse_projections(&mut self, mut expr: Syntax) -> ParserResult<Syntax> {
        loop {
            // Check for projection or method call
            if self.peek() == Some('.') && self.input().peek_nth(1).is_some_and(|c| c != '.') {
                let dot_pos = self.position();
                self.advance(); // consume '.'

                // Parse the field/method name
                let field = if self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    // Numeric projection: x.1, x.2, etc.
                    self.number()?
                } else if self.peek().is_some_and(is_id_start) {
                    // Field projection or method name: x.field or xs.reverse
                    self.identifier()?
                } else {
                    return Err(ParseError::boxed(
                        ParseErrorKind::Expected("field name or number".to_string()),
                        self.position(),
                    ));
                };

                // Check if this is a method call by looking for arguments
                // We need to be careful here - if there's whitespace followed by an argument,
                // it's a method call. Otherwise, it's a field projection.
                // Note: Numeric projections (x.1) are never method calls
                self.skip_whitespace();

                // Try to parse method arguments (only for non-numeric projections)
                let mut method_args = Vec::new();
                let is_numeric_projection = matches!(&field, Syntax::Atom(atom) if atom.value.as_str().chars().all(|c| c.is_ascii_digit()));
                let is_method_call = if !is_numeric_projection && !self.at_term_boundary() {
                    // Save position in case this isn't actually a method call
                    self.input_mut().save_position();

                    // Try to parse arguments
                    while let Ok(arg) = self.try_parse(|p| p.atom_term()) {
                        method_args.push(arg);
                        self.skip_whitespace();

                        // Check if we can parse more arguments
                        if self.at_term_boundary() || self.peek_binary_operator().is_some() {
                            break;
                        }
                    }

                    if method_args.is_empty() {
                        // No arguments parsed, restore position
                        self.input_mut().restore_position();
                        false
                    } else {
                        // We have arguments, commit the position
                        self.input_mut().commit_position();
                        true
                    }
                } else {
                    false
                };

                // Create appropriate node
                let range = self.input().range_from(dot_pos);
                if is_method_call {
                    // Method call: create an application node
                    let mut children = vec![expr, field];
                    children.extend(method_args);

                    expr = Syntax::Node(Box::new(SyntaxNode::new(
                        SyntaxKind::App,
                        range,
                        children.into(),
                    )));
                } else {
                    // Field projection
                    expr = Syntax::Node(Box::new(SyntaxNode::new(
                        SyntaxKind::Projection,
                        range,
                        smallvec![expr, field],
                    )));
                }
            } else {
                break;
            }
        }
        Ok(expr)
    }

    /// Parse do block: `do statements...`
    pub fn do_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("do")?;
        self.skip_whitespace();

        let mut statements = Vec::new();

        // Parse statements in the do block
        // Each statement can be on its own line or separated by semicolons
        loop {
            self.skip_whitespace();

            // Check for end of do block
            if self.at_block_end() {
                break;
            }

            // Parse different statement types
            if self.peek_keyword("let") {
                statements.push(self.do_let_stmt()?);
            } else if self.peek_keyword("return") {
                statements.push(self.do_return_stmt()?);
            } else if self.peek_keyword("pure") {
                statements.push(self.do_pure_stmt()?);
            } else if self.peek_keyword("for") {
                statements.push(self.do_for_stmt()?);
            } else {
                // Expression statement (possibly with bind)
                statements.push(self.do_expr_stmt()?);
            }

            self.skip_whitespace();

            // Check for statement separator
            if self.peek() == Some(';') {
                self.advance();
                self.skip_whitespace();
            } else if !self.at_line_start() && !self.at_block_end() {
                // If we're not at a line start or block end, we need a separator
                // This is a bit lenient for now
                continue;
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Do,
            range,
            statements.into(),
        ))))
    }

    /// Parse do-let statement: `let x := expr` or `let x ← expr`
    fn do_let_stmt(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("let")?;
        self.skip_whitespace();

        // Check for 'mut' keyword
        let _is_mut = if self.peek_keyword("mut") {
            self.keyword("mut")?;
            self.skip_whitespace();
            true
        } else {
            false
        };

        let pattern = self.identifier()?; // TODO: Support full patterns
        self.skip_whitespace();

        // Check for type annotation
        let ty = if self.peek() == Some(':') && self.input().peek_nth(1) != Some('=') {
            self.advance(); // consume ':'
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        self.skip_whitespace();

        // Check for bind operator ← or assignment :=
        let is_bind = if self.peek() == Some('←') {
            self.advance(); // consume ←
            true
        } else if self.peek() == Some('<') && self.input().peek_nth(1) == Some('-') {
            self.advance(); // consume <
            self.advance(); // consume -
            true
        } else {
            self.expect_char(':')?;
            self.expect_char('=')?;
            false
        };

        self.skip_whitespace();
        let value = self.term()?;

        let range = self.input().range_from(start);
        let mut children = vec![pattern];
        if let Some(ty) = ty {
            children.push(ty);
        }
        children.push(value);

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            if is_bind {
                SyntaxKind::Bind
            } else {
                SyntaxKind::Let
            },
            range,
            children.into(),
        ))))
    }

    /// Parse do-return statement: `return expr`
    fn do_return_stmt(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("return")?;
        self.skip_whitespace();

        let expr = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Return,
            range,
            smallvec![expr],
        ))))
    }

    /// Parse do-pure statement: `pure expr`
    fn do_pure_stmt(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("pure")?;
        self.skip_whitespace();

        let expr = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Return, // Reuse Return kind for pure
            range,
            smallvec![expr],
        ))))
    }

    /// Parse do-for statement: `for x in xs do body`
    fn do_for_stmt(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("for")?;
        self.skip_whitespace();

        let pattern = self.identifier()?; // TODO: Support full patterns
        self.skip_whitespace();

        self.keyword("in")?;
        self.skip_whitespace();

        let collection = self.term()?;
        self.skip_whitespace();

        self.keyword("do")?;
        self.skip_whitespace();

        // Parse the body (single statement or block)
        let body = if self.peek() == Some('{') {
            // Block
            self.do_term()?
        } else {
            // Single statement
            self.do_expr_stmt()?
        };

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::Do, // Reuse Do kind for for loops
            range,
            smallvec![pattern, collection, body],
        ))))
    }

    /// Parse do expression statement: `expr` or `pat ← expr`
    fn do_expr_stmt(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Try to parse as bind first: pattern ← expr
        if let Ok((pattern, expr)) = self.try_parse(|p| {
            let pattern = p.identifier()?; // TODO: Support full patterns
            p.skip_whitespace();

            // Check for bind operator
            if p.peek() == Some('←') {
                p.advance();
            } else if p.peek() == Some('<') && p.input().peek_nth(1) == Some('-') {
                p.advance();
                p.advance();
            } else {
                return Err(ParseError::boxed(
                    ParseErrorKind::Expected("bind operator".to_string()),
                    p.position(),
                ));
            }

            p.skip_whitespace();
            let expr = p.term()?;
            Ok((pattern, expr))
        }) {
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode::new(
                SyntaxKind::Bind,
                range,
                smallvec![pattern, expr],
            ))))
        } else {
            // Just a plain expression
            self.term()
        }
    }

    /// Check if we're at the start of a new line
    fn at_line_start(&self) -> bool {
        // Check if current position is at column 1
        let current_pos = self.position();
        current_pos.column == 1
    }

    /// Parse centered dot placeholder: `·`
    pub fn cdot_placeholder(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('·')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Atom(SyntaxAtom::new(
            range,
            BaseCoword::new("·"),
        )))
    }
}
