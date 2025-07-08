use crate::error::{ParseError, ParseErrorKind};
use crate::input::Input;
use lean_syn_expr::{Syntax, SourcePos};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub type ParserResult<T> = Result<T, ParseError>;

pub struct Parser<'a> {
    input: Input<'a>,
    memo_table: Rc<RefCell<HashMap<(usize, &'static str), MemoEntry>>>,
}

#[derive(Clone)]
enum MemoEntry {
    Success(Syntax, usize),
    Failure(ParseError),
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            input: Input::new(source),
            memo_table: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub fn input(&self) -> &Input<'a> {
        &self.input
    }

    pub fn input_mut(&mut self) -> &mut Input<'a> {
        &mut self.input
    }

    pub fn position(&self) -> SourcePos {
        self.input.position()
    }

    pub fn peek(&self) -> Option<char> {
        self.input.peek()
    }

    pub fn advance(&mut self) -> Option<char> {
        self.input.advance()
    }

    pub fn expect_char(&mut self, expected: char) -> ParserResult<()> {
        match self.peek() {
            Some(ch) if ch == expected => {
                self.advance();
                Ok(())
            }
            Some(_ch) => Err(ParseError::new(
                ParseErrorKind::Expected(format!("'{}'", expected)),
                self.position(),
            )),
            None => Err(ParseError::new(
                ParseErrorKind::UnexpectedEof,
                self.position(),
            )),
        }
    }

    pub fn consume_while<F>(&mut self, predicate: F) -> String
    where
        F: FnMut(char) -> bool,
    {
        self.input.consume_while(predicate)
    }

    pub fn try_parse<F, T>(&mut self, f: F) -> ParserResult<T>
    where
        F: FnOnce(&mut Self) -> ParserResult<T>,
    {
        self.input.save_position();
        match f(self) {
            Ok(result) => {
                self.input.commit_position();
                Ok(result)
            }
            Err(e) => {
                self.input.restore_position();
                Err(e)
            }
        }
    }

    pub fn memoized<F>(&mut self, rule_name: &'static str, f: F) -> ParserResult<Syntax>
    where
        F: FnOnce(&mut Self) -> ParserResult<Syntax>,
    {
        let key = (self.input.position().offset, rule_name);
        
        if let Some(entry) = self.memo_table.borrow().get(&key) {
            match entry {
                MemoEntry::Success(syntax, new_offset) => {
                    // Fast-forward input to memoized position
                    while self.input.position().offset < *new_offset {
                        self.input.advance();
                    }
                    return Ok(syntax.clone());
                }
                MemoEntry::Failure(err) => return Err(err.clone()),
            }
        }

        let _start_offset = self.input.position().offset;
        match f(self) {
            Ok(syntax) => {
                let end_offset = self.input.position().offset;
                self.memo_table.borrow_mut().insert(
                    key,
                    MemoEntry::Success(syntax.clone(), end_offset),
                );
                Ok(syntax)
            }
            Err(err) => {
                self.memo_table.borrow_mut().insert(
                    key,
                    MemoEntry::Failure(err.clone()),
                );
                Err(err)
            }
        }
    }

    pub fn skip_whitespace(&mut self) {
        self.consume_while(|ch| ch.is_whitespace());
    }

    pub fn skip_whitespace_and_comments(&mut self) {
        loop {
            self.skip_whitespace();
            if self.peek() == Some('-') && self.input.peek_nth(1) == Some('-') {
                self.advance();
                self.advance();
                self.consume_while(|ch| ch != '\n');
            } else if self.peek() == Some('/') && self.input.peek_nth(1) == Some('-') {
                self.advance();
                self.advance();
                self.skip_block_comment();
            } else {
                break;
            }
        }
    }

    fn skip_block_comment(&mut self) {
        let mut depth = 1;
        while depth > 0 {
            match (self.peek(), self.input.peek_nth(1)) {
                (Some('/'), Some('-')) => {
                    self.advance();
                    self.advance();
                    depth += 1;
                }
                (Some('-'), Some('/')) => {
                    self.advance();
                    self.advance();
                    depth -= 1;
                }
                (Some(_), _) => {
                    self.advance();
                }
                (None, _) => break,
            }
        }
    }

    pub fn identifier(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        if !self.peek().map_or(false, |ch| is_id_start(ch)) {
            return Err(ParseError::new(
                ParseErrorKind::Expected("identifier".to_string()),
                start,
            ));
        }
        
        let name = self.consume_while(|ch| is_id_continue(ch));
        let range = self.input().range_from(start);
        
        Ok(Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range,
            value: eterned::BaseCoword::new(name),
        }))
    }

    pub fn keyword(&mut self, kw: &str) -> ParserResult<()> {
        let start = self.position();
        
        if !self.peek_keyword(kw) {
            return Err(ParseError::new(
                ParseErrorKind::Expected(format!("keyword '{}'", kw)),
                start,
            ));
        }
        
        // Consume the keyword
        for _ in kw.chars() {
            self.advance();
        }
        
        Ok(())
    }

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

    pub fn number(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        if !self.peek().map_or(false, |ch| ch.is_ascii_digit()) {
            return Err(ParseError::new(
                ParseErrorKind::Expected("number".to_string()),
                start,
            ));
        }
        
        let num = self.consume_while(|ch| ch.is_ascii_digit() || ch == '.');
        let range = self.input().range_from(start);
        
        Ok(Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range,
            value: eterned::BaseCoword::new(num),
        }))
    }

    pub fn string_literal(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.expect_char('"')?;
        let mut content = String::new();
        
        while let Some(ch) = self.peek() {
            if ch == '"' {
                self.advance();
                break;
            } else if ch == '\\' {
                self.advance();
                match self.peek() {
                    Some('n') => {
                        self.advance();
                        content.push('\n');
                    }
                    Some('t') => {
                        self.advance();
                        content.push('\t');
                    }
                    Some('r') => {
                        self.advance();
                        content.push('\r');
                    }
                    Some('\\') => {
                        self.advance();
                        content.push('\\');
                    }
                    Some('"') => {
                        self.advance();
                        content.push('"');
                    }
                    _ => {
                        return Err(ParseError::new(
                            ParseErrorKind::Custom("invalid escape sequence".to_string()),
                            self.position(),
                        ));
                    }
                }
            } else {
                content.push(ch);
                self.advance();
            }
        }
        
        let range = self.input().range_from(start);
        Ok(Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range,
            value: eterned::BaseCoword::new(content),
        }))
    }

    pub fn char_literal(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.expect_char('\'')?;
        
        let ch = match self.peek() {
            Some('\\') => {
                self.advance();
                match self.peek() {
                    Some('n') => {
                        self.advance();
                        '\n'
                    }
                    Some('t') => {
                        self.advance();
                        '\t'
                    }
                    Some('r') => {
                        self.advance();
                        '\r'
                    }
                    Some('\\') => {
                        self.advance();
                        '\\'
                    }
                    Some('\'') => {
                        self.advance();
                        '\''
                    }
                    _ => {
                        return Err(ParseError::new(
                            ParseErrorKind::Custom("invalid escape sequence".to_string()),
                            self.position(),
                        ));
                    }
                }
            }
            Some(c) => {
                self.advance();
                c
            }
            None => {
                return Err(ParseError::new(
                    ParseErrorKind::UnexpectedEof,
                    self.position(),
                ));
            }
        };
        
        self.expect_char('\'')?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range,
            value: eterned::BaseCoword::new(ch.to_string()),
        }))
    }

    /// Parse a binder group: `(x y : α)` or `{α : Type}` or `[inst : Functor F]`
    pub fn binder_group(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        let (_open_delim, close_delim, binder_kind) = match self.peek() {
            Some('(') => ('(', ')', lean_syn_expr::SyntaxKind::LeftParen),
            Some('{') => ('{', '}', lean_syn_expr::SyntaxKind::LeftBrace),
            Some('[') => ('[', ']', lean_syn_expr::SyntaxKind::LeftBracket),
            _ => return Err(ParseError::new(
                ParseErrorKind::Expected("binder".to_string()),
                start,
            )),
        };
        
        self.advance(); // consume opening delimiter
        self.skip_whitespace();
        
        let mut names = Vec::new();
        
        // Parse names
        while self.peek().map_or(false, |ch| is_id_start(ch)) {
            names.push(self.identifier()?);
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
        
        self.skip_whitespace();
        self.expect_char(close_delim)?;
        
        let range = self.input().range_from(start);
        let mut children = names;
        if let Some(t) = ty {
            children.push(t);
        }
        
        Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
            kind: binder_kind,
            range,
            children: children.into(),
        })))
    }
}

fn is_id_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_id_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '?' || ch == '!'
}