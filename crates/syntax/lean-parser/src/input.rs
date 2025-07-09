use std::str::Chars;

use lean_syn_expr::{SourcePos, SourceRange};

#[derive(Clone)]
pub struct Input<'a> {
    source: &'a str,
    chars: Chars<'a>,
    position: SourcePos,
    saved_positions: Vec<(Chars<'a>, SourcePos)>,
}

impl<'a> Input<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.chars(),
            position: SourcePos::new(1, 1, 0),
            saved_positions: Vec::new(),
        }
    }

    pub fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    pub fn peek_nth(&self, n: usize) -> Option<char> {
        self.chars.clone().nth(n)
    }

    pub fn advance(&mut self) -> Option<char> {
        if let Some(ch) = self.chars.next() {
            self.position.offset += ch.len_utf8();
            if ch == '\n' {
                self.position.line += 1;
                self.position.column = 1;
            } else {
                self.position.column += 1;
            }
            Some(ch)
        } else {
            None
        }
    }

    pub fn consume_while<F>(&mut self, mut predicate: F) -> String
    where
        F: FnMut(char) -> bool,
    {
        let mut result = String::new();
        while let Some(ch) = self.peek() {
            if predicate(ch) {
                result.push(ch);
                self.advance();
            } else {
                break;
            }
        }
        result
    }

    pub fn position(&self) -> SourcePos {
        self.position
    }

    pub fn range_from(&self, start: SourcePos) -> SourceRange {
        SourceRange {
            start,
            end: self.position,
        }
    }

    pub fn save_position(&mut self) {
        self.saved_positions
            .push((self.chars.clone(), self.position));
    }

    pub fn restore_position(&mut self) {
        if let Some((chars, position)) = self.saved_positions.pop() {
            self.chars = chars;
            self.position = position;
        }
    }

    pub fn commit_position(&mut self) {
        self.saved_positions.pop();
    }

    pub fn source(&self) -> &'a str {
        self.source
    }

    pub fn remaining(&self) -> &'a str {
        self.chars.as_str()
    }

    pub fn is_at_end(&self) -> bool {
        self.chars.as_str().is_empty()
    }
}

pub trait ParserInput {
    fn peek(&self) -> Option<char>;
    fn advance(&mut self) -> Option<char>;
    fn position(&self) -> SourcePos;
    fn save_position(&mut self);
    fn restore_position(&mut self);
    fn commit_position(&mut self);
}
