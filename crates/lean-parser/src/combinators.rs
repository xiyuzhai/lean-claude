use crate::parser::{Parser, ParserResult};
use crate::error::{ParseError, ParseErrorKind};
use lean_syntax::{Syntax, SyntaxNode, SyntaxKind, SyntaxAtom};
use lean_eterned::BaseCoword;
use smallvec::SmallVec;

impl<'a> Parser<'a> {
    pub fn identifier(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        let first = self.peek().ok_or_else(|| {
            ParseError::new(ParseErrorKind::UnexpectedEof, start.clone())
        })?;
        
        if !is_id_start(first) {
            return Err(ParseError::new(
                ParseErrorKind::Expected("identifier".to_string()),
                start,
            ));
        }
        
        let value = self.consume_while(is_id_continue);
        let range = self.input().range_from(start);
        
        Ok(Syntax::Atom(SyntaxAtom {
            range,
            value: BaseCoword::new(value),
        }))
    }
    
    pub fn number(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        let value = self.consume_while(|ch| ch.is_ascii_digit());
        if value.is_empty() {
            return Err(ParseError::new(
                ParseErrorKind::Expected("number".to_string()),
                start,
            ));
        }
        
        // Handle decimal numbers
        if self.peek() == Some('.') && self.input().peek_nth(1).map_or(false, |ch| ch.is_ascii_digit()) {
            self.advance(); // consume '.'
            let decimal = self.consume_while(|ch| ch.is_ascii_digit());
            let full_value = format!("{}.{}", value, decimal);
            let range = self.input().range_from(start);
            
            Ok(Syntax::Atom(SyntaxAtom {
                range,
                value: BaseCoword::new(full_value),
            }))
        } else {
            let range = self.input().range_from(start);
            Ok(Syntax::Atom(SyntaxAtom {
                range,
                value: BaseCoword::new(value),
            }))
        }
    }
    
    pub fn string_literal(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.expect_char('"')?;
        let mut value = String::new();
        
        loop {
            match self.peek() {
                Some('"') => {
                    self.advance();
                    break;
                }
                Some('\\') => {
                    self.advance();
                    match self.peek() {
                        Some('n') => {
                            self.advance();
                            value.push('\n');
                        }
                        Some('t') => {
                            self.advance();
                            value.push('\t');
                        }
                        Some('r') => {
                            self.advance();
                            value.push('\r');
                        }
                        Some('\\') => {
                            self.advance();
                            value.push('\\');
                        }
                        Some('"') => {
                            self.advance();
                            value.push('"');
                        }
                        Some(ch) => {
                            self.advance();
                            value.push(ch);
                        }
                        None => {
                            return Err(ParseError::new(
                                ParseErrorKind::UnterminatedString,
                                self.position(),
                            ));
                        }
                    }
                }
                Some(ch) => {
                    value.push(ch);
                    self.advance();
                }
                None => {
                    return Err(ParseError::new(
                        ParseErrorKind::UnterminatedString,
                        self.position(),
                    ));
                }
            }
        }
        
        let range = self.input().range_from(start);
        Ok(Syntax::Atom(SyntaxAtom {
            range,
            value: BaseCoword::new(value),
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
                    Some(ch) => {
                        self.advance();
                        ch
                    }
                    None => {
                        return Err(ParseError::new(
                            ParseErrorKind::InvalidChar,
                            self.position(),
                        ));
                    }
                }
            }
            Some(ch) => {
                self.advance();
                ch
            }
            None => {
                return Err(ParseError::new(
                    ParseErrorKind::InvalidChar,
                    self.position(),
                ));
            }
        };
        
        self.expect_char('\'')?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Atom(SyntaxAtom {
            range,
            value: BaseCoword::new(ch.to_string()),
        }))
    }
    
    pub fn keyword(&mut self, kw: &str) -> ParserResult<()> {
        let start = self.position();
        
        for expected_ch in kw.chars() {
            match self.peek() {
                Some(ch) if ch == expected_ch => {
                    self.advance();
                }
                _ => {
                    return Err(ParseError::new(
                        ParseErrorKind::Expected(format!("keyword '{}'", kw)),
                        start,
                    ));
                }
            }
        }
        
        // Ensure keyword is not part of a larger identifier
        if let Some(ch) = self.peek() {
            if is_id_continue(ch) {
                return Err(ParseError::new(
                    ParseErrorKind::Expected(format!("keyword '{}'", kw)),
                    start,
                ));
            }
        }
        
        Ok(())
    }
    
    pub fn delimited<T, F>(
        &mut self,
        open: char,
        close: char,
        separator: Option<char>,
        mut parse_item: F,
    ) -> ParserResult<Vec<T>>
    where
        F: FnMut(&mut Self) -> ParserResult<T>,
    {
        self.expect_char(open)?;
        self.skip_whitespace_and_comments();
        
        let mut items = Vec::new();
        
        while self.peek() != Some(close) {
            items.push(parse_item(self)?);
            self.skip_whitespace_and_comments();
            
            if let Some(sep) = separator {
                if self.peek() == Some(sep) {
                    self.advance();
                    self.skip_whitespace_and_comments();
                } else if self.peek() != Some(close) {
                    return Err(ParseError::new(
                        ParseErrorKind::Expected(format!("'{}' or '{}'", sep, close)),
                        self.position(),
                    ));
                }
            }
        }
        
        self.expect_char(close)?;
        Ok(items)
    }
}

fn is_id_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_id_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '?' || ch == '!'
}