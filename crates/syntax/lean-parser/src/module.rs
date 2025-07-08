use crate::parser::{Parser, ParserResult};
use crate::error::{ParseError, ParseErrorKind};
use lean_syn_expr::{Syntax, SyntaxNode, SyntaxKind, SyntaxAtom};
use eterned::BaseCoword;
use smallvec::smallvec;

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
                    // Try to recover by skipping to next line
                    self.skip_to_next_line();
                    // For now, return the error
                    return Err(e);
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
        if self.peek().map_or(false, |ch| is_id_start(ch)) {
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
        if self.peek().map_or(false, |ch| is_id_start(ch)) {
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
        while self.peek() == Some('.') && self.input().peek_nth(1).map_or(false, |ch| is_id_start(ch)) {
            self.advance(); // consume '.'
            parts.push(self.identifier()?);
        }
        
        // Create a single atom with the full path
        let path = parts.iter()
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
    
    // Placeholder implementations for other commands
    pub fn def_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("def")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("def command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn theorem_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("theorem")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("theorem command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn axiom_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("axiom")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("axiom command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn constant_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("constant")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("constant command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn variable_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("variable")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("variable command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn universe_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("universe")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("universe command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn instance_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("instance")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("instance command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn class_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("class")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("class command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn structure_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("structure")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("structure command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn inductive_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.keyword("inductive")?;
        Err(ParseError::new(
            ParseErrorKind::Custom("inductive command not yet implemented".to_string()),
            start,
        ))
    }
    
    pub fn hash_command(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.advance(); // consume '#'
        Err(ParseError::new(
            ParseErrorKind::Custom("hash command not yet implemented".to_string()),
            start,
        ))
    }
    
    /// Check if the upcoming text matches a keyword
    pub fn peek_keyword(&self, keyword: &str) -> bool {
        let mut chars = self.input().remaining().chars();
        
        for expected_ch in keyword.chars() {
            match chars.next() {
                Some(ch) if ch == expected_ch => continue,
                _ => return false,
            }
        }
        
        // Ensure keyword is not part of a larger identifier
        match chars.next() {
            Some(ch) if is_id_continue(ch) => false,
            _ => true,
        }
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

fn is_id_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_id_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '?' || ch == '!'
}