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
}