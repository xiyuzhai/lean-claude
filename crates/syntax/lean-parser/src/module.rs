use eterned::BaseCoword;
use lean_syn_expr::{Syntax, SyntaxAtom, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    lexical::is_id_start,
    parser::{Parser, ParserResult},
    recovery::RecoveryStrategy,
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
                Err(e) => {
                    // If we're at the end of input after whitespace/comments, that's fine
                    if self.input().is_at_end() {
                        break;
                    }

                    // Check if we should attempt recovery
                    if self.should_attempt_recovery() {
                        // Try to recover by skipping to next statement
                        match self.recover_from_error(e, RecoveryStrategy::SkipToNextStatement) {
                            Ok(error_node) => {
                                // Include the error node in the parse tree
                                commands.push(error_node);
                            }
                            Err(_) => {
                                // Recovery failed, stop parsing if too many errors
                                if self.too_many_errors() {
                                    break;
                                }
                            }
                        }
                    } else {
                        // Too many errors, stop parsing
                        break;
                    }
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

        // Check for keywords - must check longer keywords first to avoid prefix
        // conflicts
        if let Some(ch) = self.peek() {
            match ch {
                'a' => {
                    if self.peek_keyword("abbrev") {
                        self.abbrev_command()
                    } else if self.peek_keyword("axiom") {
                        self.axiom_command()
                    } else {
                        Err(ParseError::boxed(
                            ParseErrorKind::Expected("command".to_string()),
                            start,
                        ))
                    }
                }
                'c' => {
                    if self.peek_keyword("class") {
                        self.class_command()
                    } else if self.peek_keyword("constant") {
                        self.constant_command()
                    } else {
                        Err(ParseError::boxed(
                            ParseErrorKind::Expected("command".to_string()),
                            start,
                        ))
                    }
                }
                'd' => {
                    if self.peek_keyword("declare_syntax_cat") {
                        self.declare_syntax_cat()
                    } else if self.peek_keyword("def") {
                        self.def_command()
                    } else {
                        Err(ParseError::boxed(
                            ParseErrorKind::Expected("command".to_string()),
                            start,
                        ))
                    }
                }
                'e' => {
                    if self.peek_keyword("elab") {
                        self.elab_command()
                    } else if self.peek_keyword("end") {
                        self.end_command()
                    } else {
                        Err(ParseError::boxed(
                            ParseErrorKind::Expected("command".to_string()),
                            start,
                        ))
                    }
                }
                'i' => {
                    if self.peek_keyword("inductive") {
                        self.inductive_command()
                    } else if self.peek_keyword("instance") {
                        self.instance_command()
                    } else if self.peek_keyword("import") {
                        self.import_command()
                    } else {
                        Err(ParseError::boxed(
                            ParseErrorKind::Expected("command".to_string()),
                            start,
                        ))
                    }
                }
                'm' => {
                    if self.peek_keyword("macro_rules") {
                        self.macro_rules()
                    } else if self.peek_keyword("macro") {
                        self.macro_def()
                    } else if self.peek_keyword("mutual") {
                        self.mutual_command()
                    } else {
                        Err(ParseError::boxed(
                            ParseErrorKind::Expected("command".to_string()),
                            start,
                        ))
                    }
                }
                'n' => {
                    if self.peek_keyword("notation") {
                        self.notation_def()
                    } else if self.peek_keyword("namespace") {
                        self.namespace_command()
                    } else {
                        Err(ParseError::boxed(
                            ParseErrorKind::Expected("command".to_string()),
                            start,
                        ))
                    }
                }
                'o' if self.peek_keyword("open") => self.open_command(),
                's' => {
                    if self.peek_keyword("structure") {
                        self.structure_command()
                    } else if self.peek_keyword("syntax") {
                        self.syntax_def()
                    } else if self.peek_keyword("section") {
                        self.section_command()
                    } else {
                        Err(ParseError::boxed(
                            ParseErrorKind::Expected("command".to_string()),
                            start,
                        ))
                    }
                }
                't' if self.peek_keyword("theorem") => self.theorem_command(),
                'u' if self.peek_keyword("universe") => self.universe_command(),
                'v' if self.peek_keyword("variable") => self.variable_command(),
                '#' => self.hash_command(),
                '-' if self.input().peek_nth(1) == Some('-') => {
                    // Line comment, not a command
                    Err(ParseError::boxed(
                        ParseErrorKind::Expected("command".to_string()),
                        start,
                    ))
                }
                '/' if self.input().peek_nth(1) == Some('-') => {
                    // Block comment, not a command
                    Err(ParseError::boxed(
                        ParseErrorKind::Expected("command".to_string()),
                        start,
                    ))
                }
                _ => Err(ParseError::boxed(
                    ParseErrorKind::Expected("command".to_string()),
                    start,
                )),
            }
        } else {
            Err(ParseError::boxed(ParseErrorKind::UnexpectedEof, start))
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

    /// Parse elab command: `elab "name" args : type => body`
    pub fn elab_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("elab")?;
        self.skip_whitespace();

        let mut children = Vec::new();

        // Parse optional attributes
        if self.peek() == Some('[') {
            children.push(self.parse_attributes()?);
            self.skip_whitespace();
        }

        // Parse name (string literal or identifier)
        let name = if self.peek() == Some('"') {
            self.string_literal()?
        } else {
            self.identifier()?
        };
        children.push(name);
        self.skip_whitespace();

        // Parse parameters
        while self.peek() == Some('{')
            || self.peek() == Some('[')
            || self.peek() == Some('(')
            || (self.peek().is_some_and(is_id_start) && !self.peek_keyword(":"))
        {
            if self.peek().is_some_and(is_id_start) {
                // Simple parameter like x:term
                let param = self.identifier()?;
                children.push(param);
                self.skip_whitespace();

                if self.peek() == Some(':') {
                    self.advance();
                    self.skip_whitespace();
                    let cat = self.identifier()?;
                    children.push(cat);
                    self.skip_whitespace();
                }
            } else {
                // Binder group
                children.push(self.binder_group()?);
                self.skip_whitespace();
            }
        }

        // Parse result type
        self.expect_char(':')?;
        self.skip_whitespace();
        let result_type = self.term()?;
        children.push(result_type);
        self.skip_whitespace();

        // Parse arrow
        self.expect_char('=')?;
        self.expect_char('>')?;
        self.skip_whitespace();

        // Parse body
        let body = self.term()?;
        children.push(body);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Elab,
            range,
            children: children.into(),
        })))
    }
}
