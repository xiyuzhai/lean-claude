use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    lexical::is_id_start,
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse def command: `def name [params] : type := value`
    pub fn def_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        // Check for attributes before the command
        let has_attrs = self.peek() == Some('@') || (self.peek() == Some('[') && self.peek_attribute_list());
        let attrs = if has_attrs {
            Some(self.parse_attributes()?)
        } else {
            None
        };
        self.skip_whitespace();

        self.keyword("def")?;
        self.skip_whitespace();

        // Parse name
        let name = self.identifier()?;
        self.skip_whitespace();

        // Parse optional type parameters
        let mut params = Vec::new();
        while self.peek() == Some('{') || self.peek() == Some('[') || self.peek() == Some('(') {
            params.push(self.binder_group()?);
            self.skip_whitespace();
        }

        // Parse type annotation
        let ty = if self.peek() == Some(':') {
            self.advance(); // consume ':'
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        // Parse definition - always expect ':='
        self.skip_whitespace();
        self.expect_char(':')?;
        self.expect_char('=')?;
        self.skip_whitespace();

        let value = self.term()?;

        let range = self.input().range_from(start);
        let mut children = smallvec![];
        if let Some(attrs) = attrs {
            children.push(attrs);
        }
        children.push(name);
        children.extend(params);
        if let Some(ty) = ty {
            children.push(ty);
        }
        children.push(value);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Def,
            range,
            children,
        })))
    }

    /// Parse theorem command: `theorem name [params] : type := proof`
    pub fn theorem_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("theorem")?;
        self.skip_whitespace();

        // Parse name
        let name = self.identifier()?;
        self.skip_whitespace();

        // Parse optional type parameters
        let mut params = Vec::new();
        while self.peek() == Some('{') || self.peek() == Some('[') || self.peek() == Some('(') {
            params.push(self.binder_group()?);
            self.skip_whitespace();
        }

        // Parse type
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.term()?;

        // Parse proof
        self.skip_whitespace();
        // Parse := operator
        if self.peek() == Some(':') {
            self.advance(); // consume ':'
            self.expect_char('=')?;
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected(":=".to_string()),
                self.position(),
            ));
        }
        self.skip_whitespace();

        let proof = self.term()?;

        let range = self.input().range_from(start);
        let mut children = smallvec![name];
        children.extend(params);
        children.push(ty);
        children.push(proof);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Theorem,
            range,
            children,
        })))
    }

    /// Parse variable command: `variable {α : Type} (x : α)`
    pub fn variable_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("variable")?;
        self.skip_whitespace();

        let mut binders = Vec::new();

        // Parse binder groups
        while self.peek() == Some('{') || self.peek() == Some('[') || self.peek() == Some('(') {
            binders.push(self.binder_group()?);
            self.skip_whitespace();
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Variable,
            range,
            children: binders.into(),
        })))
    }

    /// Parse universe command: `universe u v`
    pub fn universe_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("universe")?;
        self.skip_whitespace();

        let mut universes = Vec::new();

        // Parse universe names
        while self.peek().is_some_and(is_id_start) {
            universes.push(self.identifier()?);
            self.skip_whitespace();
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Universe,
            range,
            children: universes.into(),
        })))
    }

    /// Parse constant command: `constant c : Type`
    pub fn constant_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("constant")?;
        self.skip_whitespace();

        // Parse name
        let name = self.identifier()?;
        self.skip_whitespace();

        // Parse type
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Constant,
            range,
            children: smallvec![name, ty],
        })))
    }

    /// Parse axiom command: `axiom ax : Prop`
    pub fn axiom_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("axiom")?;
        self.skip_whitespace();

        // Parse name
        let name = self.identifier()?;
        self.skip_whitespace();

        // Parse type
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Axiom,
            range,
            children: smallvec![name, ty],
        })))
    }

    /// Parse instance command: `instance : Functor List := ...`
    pub fn instance_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("instance")?;
        self.skip_whitespace();

        // Optional instance name
        let name = if self.peek() != Some(':') && self.peek().is_some_and(is_id_start) {
            Some(self.identifier()?)
        } else {
            None
        };

        self.skip_whitespace();

        // Parse type
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.term()?;

        // Parse definition
        self.skip_whitespace();
        // Parse := operator
        if self.peek() == Some(':') {
            self.advance(); // consume ':'
            self.expect_char('=')?;
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected(":=".to_string()),
                self.position(),
            ));
        }
        self.skip_whitespace();

        let value = self.term()?;

        let range = self.input().range_from(start);
        let mut children = smallvec![];
        if let Some(n) = name {
            children.push(n);
        }
        children.push(ty);
        children.push(value);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Instance,
            range,
            children,
        })))
    }
}
