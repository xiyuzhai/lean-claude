use crate::parser::{Parser, ParserResult};
use crate::error::{ParseError, ParseErrorKind};
use lean_syn_expr::{Syntax, SyntaxNode, SyntaxKind};

use smallvec::smallvec;

impl<'a> Parser<'a> {
    /// Parse a term (expression)
    pub fn term(&mut self) -> ParserResult<Syntax> {
        self.arrow_term()
    }
    
    /// Parse arrow type: `α → β`
    pub fn arrow_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut left = self.app_term()?;
        
        self.skip_whitespace();
        
        // Check for arrow
        if self.peek() == Some('→') || (self.peek() == Some('-') && self.input().peek_nth(1) == Some('>')) {
            if self.peek() == Some('-') {
                self.advance(); // consume '-'
                self.advance(); // consume '>'
            } else {
                self.advance(); // consume '→'
            }
            
            self.skip_whitespace();
            let right = self.arrow_term()?;
            
            let range = self.input().range_from(start);
            left = Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::Arrow,
                range,
                children: smallvec![left, right],
            }));
        }
        
        Ok(left)
    }
    
    /// Parse application: `f x y z`
    pub fn app_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut terms = vec![self.atom_term()?];
        
        loop {
            self.skip_whitespace();
            
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
            Some(ch) if ch.is_ascii_digit() => self.number(),
            Some('"') => self.string_literal(),
            Some('\'') => self.char_literal(),
            Some(ch) if is_id_start(ch) => self.identifier(),
            Some(_) => Err(ParseError::new(
                ParseErrorKind::Expected("term".to_string()),
                self.position(),
            )),
            None => Err(ParseError::new(
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
    
    /// Parse implicit term: `{term}`
    pub fn implicit_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('{')?;
        self.skip_whitespace();
        let term = self.term()?;
        self.skip_whitespace();
        self.expect_char('}')?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::LeftBrace,
            range,
            children: smallvec![term],
        })))
    }
    
    /// Parse instance implicit term: `[term]`
    pub fn inst_implicit_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('[')?;
        self.skip_whitespace();
        let term = self.term()?;
        self.skip_whitespace();
        self.expect_char(']')?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::LeftBracket,
            range,
            children: smallvec![term],
        })))
    }
    
    /// Parse lambda: `λ x => body` or `fun x => body`
    pub fn lambda_term(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        // Consume lambda symbol
        if self.peek() == Some('λ') {
            self.advance();
        } else if self.peek() == Some('\\') {
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
            } else if self.peek().map_or(false, |ch| is_id_start(ch)) {
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
            return Err(ParseError::new(
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
            } else if self.peek().map_or(false, |ch| is_id_start(ch)) {
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
        let ty = if self.peek() == Some(':') {
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

fn is_id_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}