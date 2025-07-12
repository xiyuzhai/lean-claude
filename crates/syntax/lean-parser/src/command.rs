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
        let has_attrs =
            self.peek() == Some('@') || (self.peek() == Some('[') && self.peek_attribute_list());
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

        // Parse type annotation - but check it's not :=
        let ty = if self.peek() == Some(':') && self.input().peek_nth(1) != Some('=') {
            self.advance(); // consume ':'
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        self.skip_whitespace();

        // Parse where clause if present
        let where_clause = if self.peek_keyword("where") {
            self.keyword("where")?;
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        // Parse definition - expect ':='
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
        if let Some(where_clause) = where_clause {
            children.push(where_clause);
        }
        children.push(value);

        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Def, range, children))))
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

        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Theorem, range, children))))
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
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Variable, range, binders.into()))))
    }

    /// Parse example command: `example : type := proof`
    pub fn example_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("example")?;
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
        let mut children = params;
        children.push(ty);
        children.push(proof);

        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Theorem, range, children.into()))))
    }

    /// Parse universe command: `universe u v`
    pub fn universe_command(&mut self) -> ParserResult<Syntax> {
        self.parse_universe_declaration()
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
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Constant, range, smallvec![name, ty]))))
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
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Axiom, range, smallvec![name, ty]))))
    }

    /// Parse instance command: `instance : Functor List := ...`
    /// Parse structure command: `structure Name [params] [extends Parent] where
    /// [fields]`
    pub fn structure_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("structure")?;
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

        // Parse optional extends clause
        let extends = if self.peek_keyword("extends") {
            self.keyword("extends")?;
            self.skip_whitespace();
            // Parse the parent type, but be careful not to consume "where"
            Some(self.atom_term()?)
        } else {
            None
        };
        self.skip_whitespace();

        // Parse where clause
        self.keyword("where")?;
        self.skip_whitespace();

        // Parse fields
        let mut fields = Vec::new();
        while self.peek().is_some_and(is_id_start) {
            // Check if this might be a command keyword rather than a field
            if self.is_at_command_keyword() {
                break;
            }
            fields.push(self.structure_field()?);
            self.skip_whitespace();
        }

        // Parse optional deriving clause
        let deriving = if self.peek_keyword("deriving") {
            Some(self.deriving_clause()?)
        } else {
            None
        };

        let mut children = smallvec![name];
        children.extend(params);
        if let Some(ext) = extends {
            children.push(ext);
        }
        children.extend(fields);
        if let Some(d) = deriving {
            children.push(d);
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Structure, range, children))))
    }

    /// Parse a structure field: `fieldName : Type`
    fn structure_field(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let field_name = self.identifier()?;
        self.skip_whitespace();

        self.expect_char(':')?;
        self.skip_whitespace();

        // For fields, parse a single atomic term to avoid consuming across lines
        // This prevents the term parser from treating subsequent fields as applications
        let field_type = self.atom_term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Field, range, smallvec![field_name, field_type]))))
    }

    /// Parse inductive command: `inductive Name [params] where [constructors]`
    pub fn inductive_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("inductive")?;
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

        // Optional type annotation
        let ty = if self.peek() == Some(':') {
            self.advance(); // consume ':'
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };
        self.skip_whitespace();

        // Parse where clause or := for constructors
        let mut constructors = Vec::new();
        if self.peek_keyword("where") {
            self.keyword("where")?;
            self.skip_whitespace();

            // Parse constructors
            while self.peek() == Some('|')
                || (constructors.is_empty() && self.peek().is_some_and(is_id_start))
            {
                // Check if this might be a command keyword rather than a constructor
                if self.peek().is_some_and(is_id_start) && self.is_at_command_keyword() {
                    break;
                }
                if self.peek() == Some('|') {
                    self.advance(); // consume '|'
                    self.skip_whitespace();
                }
                constructors.push(self.inductive_constructor()?);
                self.skip_whitespace();
            }
        }

        // Parse optional deriving clause
        let deriving = if self.peek_keyword("deriving") {
            Some(self.deriving_clause()?)
        } else {
            None
        };

        let mut children = smallvec![name];
        children.extend(params);
        if let Some(t) = ty {
            children.push(t);
        }
        children.extend(constructors);
        if let Some(d) = deriving {
            children.push(d);
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Inductive, range, children))))
    }

    /// Parse an inductive constructor: `ConstructorName [: Type]`
    fn inductive_constructor(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let ctor_name = self.identifier()?;
        self.skip_whitespace();

        // Type annotation is optional
        let ctor_type = if self.peek() == Some(':') {
            self.advance(); // consume ':'
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        let range = self.input().range_from(start);
        let mut children = smallvec![ctor_name];
        if let Some(ty) = ctor_type {
            children.push(ty);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Constructor, range, children))))
    }

    /// Parse class command: `class Name [params] [extends Parent] where
    /// [fields]`
    pub fn class_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("class")?;
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

        // Parse optional extends clause
        let extends = if self.peek_keyword("extends") {
            self.keyword("extends")?;
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };
        self.skip_whitespace();

        // Parse where clause
        let mut fields = Vec::new();
        if self.peek_keyword("where") {
            self.keyword("where")?;
            self.skip_whitespace();

            // Parse fields/methods
            while self.peek().is_some_and(is_id_start) {
                // Check if this might be a command keyword rather than a field
                if self.is_at_command_keyword() {
                    break;
                }
                fields.push(self.structure_field()?);
                self.skip_whitespace();
            }
        }

        let mut children = smallvec![name];
        children.extend(params);
        if let Some(ext) = extends {
            children.push(ext);
        }
        children.extend(fields);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Class, range, children))))
    }

    /// Parse abbrev command: `abbrev Name [params] := Type`
    /// Check if we're at a command keyword
    fn is_at_command_keyword(&self) -> bool {
        self.peek_keyword("def")
            || self.peek_keyword("theorem")
            || self.peek_keyword("axiom")
            || self.peek_keyword("constant")
            || self.peek_keyword("variable")
            || self.peek_keyword("universe")
            || self.peek_keyword("import")
            || self.peek_keyword("open")
            || self.peek_keyword("namespace")
            || self.peek_keyword("section")
            || self.peek_keyword("end")
            || self.peek_keyword("instance")
            || self.peek_keyword("class")
            || self.peek_keyword("structure")
            || self.peek_keyword("inductive")
            || self.peek_keyword("abbrev")
            || self.peek_keyword("macro")
            || self.peek_keyword("macro_rules")
            || self.peek_keyword("syntax")
            || self.peek_keyword("notation")
            || self.peek_keyword("elab")
            || self.peek_keyword("declare_syntax_cat")
            || self.peek_keyword("mutual")
            || self.peek_keyword("deriving")
    }

    /// Parse mutual command: `mutual ... end`
    pub fn mutual_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("mutual")?;
        self.skip_whitespace();

        // Parse the body of the mutual block - a sequence of definitions
        let mut declarations = Vec::new();

        while !self.peek_keyword("end") && !self.input().is_at_end() {
            self.skip_whitespace_and_comments();

            if self.peek_keyword("end") || self.input().is_at_end() {
                break;
            }

            // Parse a declaration inside the mutual block
            // This can be inductive, structure, def, theorem, etc.
            let decl = self.mutual_declaration()?;
            declarations.push(decl);
            self.skip_whitespace();
        }

        // Parse the closing 'end'
        self.keyword("end")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Mutual, range, declarations.into()))))
    }

    /// Parse a declaration inside a mutual block
    fn mutual_declaration(&mut self) -> ParserResult<Syntax> {
        // A mutual declaration can be any of the recursive declaration types
        match self.peek() {
            Some('i') if self.peek_keyword("inductive") => self.inductive_command(),
            Some('s') if self.peek_keyword("structure") => self.structure_command(),
            Some('d') if self.peek_keyword("def") => self.def_command(),
            Some('t') if self.peek_keyword("theorem") => self.theorem_command(),
            Some('a') if self.peek_keyword("axiom") => self.axiom_command(),
            Some('c') if self.peek_keyword("constant") => self.constant_command(),
            Some('v') if self.peek_keyword("variable") => self.variable_command(),
            Some('i') if self.peek_keyword("instance") => self.instance_command(),
            Some('c') if self.peek_keyword("class") => self.class_command(),
            Some('a') if self.peek_keyword("abbrev") => self.abbrev_command(),
            _ => Err(ParseError::boxed(
                ParseErrorKind::Expected("mutual declaration".to_string()),
                self.position(),
            )),
        }
    }

    /// Parse deriving clause: `deriving Repr, BEq, Hashable`
    fn deriving_clause(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("deriving")?;
        self.skip_whitespace();

        // Parse comma-separated list of typeclass names
        let mut typeclasses = Vec::new();

        // Parse first typeclass
        typeclasses.push(self.identifier()?);
        self.skip_whitespace();

        // Parse additional typeclasses separated by commas
        while self.peek() == Some(',') {
            self.advance(); // consume ','
            self.skip_whitespace();
            typeclasses.push(self.identifier()?);
            self.skip_whitespace();
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Deriving, range, typeclasses.into()))))
    }

    pub fn abbrev_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("abbrev")?;
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

        // Parse optional type annotation - but check it's not :=
        let ty = if self.peek() == Some(':') && self.input().peek_nth(1) != Some('=') {
            self.advance(); // consume ':'
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        // Parse definition (:=)
        self.skip_whitespace();
        if self.peek() == Some(':') && self.input().peek_nth(1) == Some('=') {
            self.advance(); // consume ':'
            self.advance(); // consume '='
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected(":=".to_string()),
                self.position(),
            ));
        }
        self.skip_whitespace();

        let body = self.term()?;

        let mut children = smallvec![name];
        children.extend(params);
        if let Some(ty) = ty {
            children.push(ty);
        }
        children.push(body);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Abbrev, range, children))))
    }

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

        let value = if self.peek_keyword("where") {
            // For now, parse instance where clauses as a single term
            // TODO: Implement proper instance where clause parsing
            self.atom_term()?
        } else {
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

            self.atom_term()? // Use atom_term to avoid consuming too much
        };

        let range = self.input().range_from(start);
        let mut children = smallvec![];
        if let Some(n) = name {
            children.push(n);
        }
        children.push(ty);
        children.push(value);

        Ok(Syntax::Node(Box::new(SyntaxNode::new(SyntaxKind::Instance, range, children))))
    }
}
