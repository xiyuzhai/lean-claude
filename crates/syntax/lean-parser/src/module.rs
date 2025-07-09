use eterned::BaseCoword;
use lean_syn_expr::{Syntax, SyntaxAtom, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    lexical::is_id_start,
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse a module (a complete Lean file)
    pub fn module(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut commands = Vec::new();

        // Skip initial whitespace and comments
        self.skip_whitespace_and_comments();

        // Parse module header (copyright, imports, etc.)
        while !self.input().is_at_end() {
            self.skip_whitespace_and_comments();

            if self.input().is_at_end() {
                break;
            }

            // Try to parse a command
            match self.command() {
                Ok(cmd) => commands.push(cmd),
                Err(_e) => {
                    // If we're at the end of input after whitespace/comments, that's fine
                    if self.input().is_at_end() {
                        break;
                    }
                    // Otherwise, skip the current character and try again
                    // This helps recover from standalone comments or other non-command content
                    self.advance();
                }
            }

            self.skip_whitespace_and_comments();
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Module,
            range,
            children: commands.into(),
        })))
    }

    /// Parse a command (top-level declaration)
    pub fn command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Check for keywords
        if let Some(ch) = self.peek() {
            match ch {
                'i' if self.peek_keyword("import") => self.import_command(),
                'o' if self.peek_keyword("open") => self.open_command(),
                'n' if self.peek_keyword("namespace") => self.namespace_command(),
                'd' if self.peek_keyword("def") => self.def_command(),
                't' if self.peek_keyword("theorem") => self.theorem_command(),
                'a' if self.peek_keyword("axiom") => self.axiom_command(),
                'c' if self.peek_keyword("constant") => self.constant_command(),
                'v' if self.peek_keyword("variable") => self.variable_command(),
                'u' if self.peek_keyword("universe") => self.universe_command(),
                's' if self.peek_keyword("section") => self.section_command(),
                'e' if self.peek_keyword("end") => self.end_command(),
                'i' if self.peek_keyword("instance") => self.instance_command(),
                'c' if self.peek_keyword("class") => self.class_command(),
                's' if self.peek_keyword("structure") => self.structure_command(),
                'i' if self.peek_keyword("inductive") => self.inductive_command(),
                '#' => self.hash_command(),
                '-' if self.input().peek_nth(1) == Some('-') => {
                    // Line comment, not a command
                    Err(ParseError::new(
                        ParseErrorKind::Expected("command".to_string()),
                        start,
                    ))
                }
                '/' if self.input().peek_nth(1) == Some('-') => {
                    // Block comment, not a command
                    Err(ParseError::new(
                        ParseErrorKind::Expected("command".to_string()),
                        start,
                    ))
                }
                _ => Err(ParseError::new(
                    ParseErrorKind::Expected("command".to_string()),
                    start,
                )),
            }
        } else {
            Err(ParseError::new(ParseErrorKind::UnexpectedEof, start))
        }
    }

    /// Parse import statement: `import Module.Path`
    pub fn import_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("import")?;
        self.skip_whitespace();

        let module_path = self.module_path()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Import,
            range,
            children: smallvec![module_path],
        })))
    }

    /// Parse open statement: `open Module.Path`
    pub fn open_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("open")?;
        self.skip_whitespace();

        let module_path = self.module_path()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Open,
            range,
            children: smallvec![module_path],
        })))
    }

    /// Parse namespace: `namespace Name`
    pub fn namespace_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("namespace")?;
        self.skip_whitespace();

        let name = self.identifier()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Namespace,
            range,
            children: smallvec![name],
        })))
    }

    /// Parse end: `end [Name]`
    pub fn end_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("end")?;
        self.skip_whitespace();

        // Optional namespace name
        let mut children = smallvec![];
        if self.peek().is_some_and(is_id_start) {
            children.push(self.identifier()?);
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::End,
            range,
            children,
        })))
    }

    /// Parse section: `section [Name]`
    pub fn section_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("section")?;
        self.skip_whitespace();

        // Optional section name
        let mut children = smallvec![];
        if self.peek().is_some_and(is_id_start) {
            children.push(self.identifier()?);
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Section,
            range,
            children,
        })))
    }

    /// Parse module path like `Mathlib.Data.Nat.Basic`
    pub fn module_path(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut parts = Vec::new();

        // First part
        parts.push(self.identifier()?);

        // Additional parts separated by dots
        while self.peek() == Some('.') && self.input().peek_nth(1).is_some_and(is_id_start) {
            self.advance(); // consume '.'
            parts.push(self.identifier()?);
        }

        // Create a single atom with the full path
        let path = parts
            .iter()
            .map(|p| match p {
                Syntax::Atom(atom) => atom.value.as_str(),
                _ => "",
            })
            .collect::<Vec<_>>()
            .join(".");

        let range = self.input().range_from(start);
        Ok(Syntax::Atom(SyntaxAtom {
            range,
            value: BaseCoword::new(path),
        }))
    }

    pub fn class_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("class")?;
        self.skip_whitespace();

        // Parse class name
        let name = self.identifier()?;
        self.skip_whitespace();

        // Parse type parameters
        let mut params = Vec::new();
        while self.peek() == Some('{') || self.peek() == Some('[') || self.peek() == Some('(') {
            params.push(self.binder_group()?);
            self.skip_whitespace();
        }

        // Parse extends clause (optional)
        let mut extends = Vec::new();
        if self.peek_keyword("extends") {
            self.keyword("extends")?;
            self.skip_whitespace();

            // Parse parent classes
            loop {
                extends.push(self.term()?);
                self.skip_whitespace();

                if self.peek() == Some(',') {
                    self.advance();
                    self.skip_whitespace();
                } else {
                    break;
                }
            }
        }

        // Parse where clause for class body
        if self.peek_keyword("where") {
            self.keyword("where")?;
            self.skip_whitespace();
        }

        // Parse class fields
        let mut fields = Vec::new();
        while self.peek().is_some_and(is_id_start)
            && !self.peek_keyword("def")
            && !self.peek_keyword("theorem")
        {
            let field_name = self.identifier()?;
            self.skip_whitespace();

            self.expect_char(':')?;
            self.skip_whitespace();

            let field_type = self.term()?;
            self.skip_whitespace();

            let field_start = field_name
                .range()
                .map(|r| r.start)
                .unwrap_or(self.position());
            fields.push(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::Field,
                range: self.input().range_from(field_start),
                children: smallvec![field_name, field_type],
            })));
        }

        let range = self.input().range_from(start);
        let mut children = smallvec![name];
        children.extend(params);
        children.extend(extends);
        children.extend(fields);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Class,
            range,
            children,
        })))
    }

    pub fn structure_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("structure")?;
        self.skip_whitespace();

        // Parse structure name
        let name = self.identifier()?;
        self.skip_whitespace();

        // Parse type parameters
        let mut params = Vec::new();
        while self.peek() == Some('{') || self.peek() == Some('[') || self.peek() == Some('(') {
            params.push(self.binder_group()?);
            self.skip_whitespace();
        }

        // Parse extends clause (optional)
        let mut extends = Vec::new();
        if self.peek_keyword("extends") {
            self.keyword("extends")?;
            self.skip_whitespace();

            // Parse parent structures
            loop {
                extends.push(self.term()?);
                self.skip_whitespace();

                if self.peek() == Some(',') {
                    self.advance();
                    self.skip_whitespace();
                } else {
                    break;
                }
            }
        }

        // Parse where clause for structure body
        if self.peek_keyword("where") {
            self.keyword("where")?;
            self.skip_whitespace();
        }

        // Parse structure fields
        let mut fields = Vec::new();
        while self.peek().is_some_and(is_id_start) {
            let field_name = self.identifier()?;
            self.skip_whitespace();

            self.expect_char(':')?;
            self.skip_whitespace();

            let field_type = self.term()?;
            self.skip_whitespace();

            // Optional default value
            let default = if self.peek() == Some(':') && self.input().peek_nth(1) == Some('=') {
                self.advance(); // consume ':'
                self.advance(); // consume '='
                self.skip_whitespace();
                Some(self.term()?)
            } else {
                None
            };

            let field_start = field_name
                .range()
                .map(|r| r.start)
                .unwrap_or(self.position());
            let field_range = self.input().range_from(field_start);
            let mut field_children = smallvec![field_name, field_type];
            if let Some(def) = default {
                field_children.push(def);
            }

            fields.push(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::Field,
                range: field_range,
                children: field_children,
            })));

            self.skip_whitespace();
        }

        let range = self.input().range_from(start);
        let mut children = smallvec![name];
        children.extend(params);
        children.extend(extends);
        children.extend(fields);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Structure,
            range,
            children,
        })))
    }

    pub fn inductive_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("inductive")?;
        self.skip_whitespace();

        // Parse inductive name
        let name = self.identifier()?;
        self.skip_whitespace();

        // Parse type parameters
        let mut params = Vec::new();
        while self.peek() == Some('{') || self.peek() == Some('[') || self.peek() == Some('(') {
            params.push(self.binder_group()?);
            self.skip_whitespace();
        }

        // Parse type annotation (optional)
        let ty = if self.peek() == Some(':') {
            self.advance(); // consume ':'
            self.skip_whitespace();
            Some(self.term()?)
        } else {
            None
        };

        self.skip_whitespace();

        // Parse where clause or pipe for constructors
        if self.peek_keyword("where") {
            self.keyword("where")?;
            self.skip_whitespace();
        }

        // Parse constructors
        let mut constructors = Vec::new();

        // First constructor might not have a pipe
        if self.peek() != Some('|') && self.peek().is_some_and(is_id_start) {
            constructors.push(self.constructor()?);
            self.skip_whitespace();
        }

        // Remaining constructors with pipes
        while self.peek() == Some('|') {
            self.advance(); // consume '|'
            self.skip_whitespace();
            constructors.push(self.constructor()?);
            self.skip_whitespace();
        }

        let range = self.input().range_from(start);
        let mut children = smallvec![name];
        children.extend(params);
        if let Some(t) = ty {
            children.push(t);
        }
        children.extend(constructors);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Inductive,
            range,
            children,
        })))
    }

    /// Parse a constructor: `name : type`
    fn constructor(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Parse constructor name
        let name = self.identifier()?;
        self.skip_whitespace();

        // Parse type
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Constructor,
            range,
            children: smallvec![name, ty],
        })))
    }

    pub fn hash_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.advance(); // consume '#'

        // Parse hash command name
        let cmd_name = self.identifier()?;
        self.skip_whitespace();

        // Parse the argument (usually a term)
        let arg = self.term()?;

        let range = self.input().range_from(start);

        // Determine the specific hash command kind
        let kind = match cmd_name.as_str() {
            "check" => SyntaxKind::HashCheck,
            "eval" => SyntaxKind::HashEval,
            "print" => SyntaxKind::HashPrint,
            "reduce" => SyntaxKind::HashReduce,
            _ => SyntaxKind::HashCommand, // Generic hash command
        };

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind,
            range,
            children: smallvec![cmd_name, arg],
        })))
    }

    /// Skip to the next line (error recovery)
    fn skip_to_next_line(&mut self) {
        while let Some(ch) = self.peek() {
            self.advance();
            if ch == '\n' {
                break;
            }
        }
    }
}
