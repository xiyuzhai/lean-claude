use std::{cell::RefCell, collections::HashMap, rc::Rc};

use lean_syn_expr::{SourcePos, Syntax};

use crate::{
    error::{ParseError, ParseErrorKind},
    input::Input,
    lexical::{is_id_continue, is_id_start},
};

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
                ParseErrorKind::Expected(format!("'{expected}'")),
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
                self.memo_table
                    .borrow_mut()
                    .insert(key, MemoEntry::Success(syntax.clone(), end_offset));
                Ok(syntax)
            }
            Err(err) => {
                self.memo_table
                    .borrow_mut()
                    .insert(key, MemoEntry::Failure(err.clone()));
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

        if !self.peek().is_some_and(is_id_start) {
            return Err(ParseError::new(
                ParseErrorKind::Expected("identifier".to_string()),
                start,
            ));
        }

        let name = self.consume_while(is_id_continue);
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
                ParseErrorKind::Expected(format!("keyword '{kw}'")),
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
        !matches!(chars.next(), Some(ch) if is_id_continue(ch))
    }

    pub fn number(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        if !self.peek().is_some_and(|ch| ch.is_ascii_digit()) {
            return Err(ParseError::new(
                ParseErrorKind::Expected("number".to_string()),
                start,
            ));
        }

        let num = if self.peek() == Some('0') {
            match self.input.peek_nth(1) {
                Some('x') | Some('X') => {
                    // Hexadecimal
                    self.advance(); // consume '0'
                    self.advance(); // consume 'x'
                    let mut hex = String::from("0x");
                    hex.push_str(&self.consume_while(|ch| ch.is_ascii_hexdigit()));
                    if hex.len() == 2 {
                        return Err(ParseError::new(
                            ParseErrorKind::Custom(
                                "hexadecimal literal must have at least one digit".to_string(),
                            ),
                            self.position(),
                        ));
                    }
                    hex
                }
                Some('b') | Some('B') => {
                    // Binary
                    self.advance(); // consume '0'
                    self.advance(); // consume 'b'
                    let mut bin = String::from("0b");
                    bin.push_str(&self.consume_while(|ch| ch == '0' || ch == '1'));
                    if bin.len() == 2 {
                        return Err(ParseError::new(
                            ParseErrorKind::Custom(
                                "binary literal must have at least one digit".to_string(),
                            ),
                            self.position(),
                        ));
                    }
                    bin
                }
                Some('o') | Some('O') => {
                    // Octal
                    self.advance(); // consume '0'
                    self.advance(); // consume 'o'
                    let mut oct = String::from("0o");
                    oct.push_str(&self.consume_while(|ch| ch >= '0' && ch <= '7'));
                    if oct.len() == 2 {
                        return Err(ParseError::new(
                            ParseErrorKind::Custom(
                                "octal literal must have at least one digit".to_string(),
                            ),
                            self.position(),
                        ));
                    }
                    oct
                }
                _ => {
                    // Regular decimal number starting with 0
                    self.parse_decimal_number()
                }
            }
        } else {
            // Regular decimal number
            self.parse_decimal_number()
        };

        let range = self.input().range_from(start);
        Ok(Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range,
            value: eterned::BaseCoword::new(num),
        }))
    }

    fn parse_decimal_number(&mut self) -> String {
        let mut num = self.consume_while(|ch| ch.is_ascii_digit());

        // Check for decimal point
        if self.peek() == Some('.') && self.input.peek_nth(1).is_some_and(|ch| ch.is_ascii_digit())
        {
            num.push('.');
            self.advance();
            num.push_str(&self.consume_while(|ch| ch.is_ascii_digit()));
        }

        // Check for scientific notation
        if matches!(self.peek(), Some('e') | Some('E')) {
            num.push(self.peek().unwrap());
            self.advance();

            // Optional sign
            if matches!(self.peek(), Some('+') | Some('-')) {
                num.push(self.peek().unwrap());
                self.advance();
            }

            // Exponent digits
            let exp = self.consume_while(|ch| ch.is_ascii_digit());
            if exp.is_empty() {
                // This is actually an error, but we'll let the compiler catch
                // it For now, we'll just return what we have
            } else {
                num.push_str(&exp);
            }
        }

        num
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

    pub fn raw_string_literal(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Consume 'r'
        self.advance();

        // Count the number of '#' symbols
        let mut hash_count = 0;
        while self.peek() == Some('#') {
            self.advance();
            hash_count += 1;
        }

        // Expect opening quote
        self.expect_char('"')?;

        let mut content = String::new();

        // Read until we find the closing pattern
        loop {
            match self.peek() {
                Some('"') => {
                    // Check if this is followed by the right number of hashes
                    let mut temp_pos = 1;
                    let mut hash_match = true;

                    for _ in 0..hash_count {
                        if self.input.peek_nth(temp_pos) != Some('#') {
                            hash_match = false;
                            break;
                        }
                        temp_pos += 1;
                    }

                    if hash_match {
                        // Consume the closing quote and hashes
                        self.advance(); // consume '"'
                        for _ in 0..hash_count {
                            self.advance(); // consume '#'
                        }
                        break;
                    } else {
                        // Not the closing pattern, just a regular quote
                        content.push('"');
                        self.advance();
                    }
                }
                Some(ch) => {
                    content.push(ch);
                    self.advance();
                }
                None => {
                    return Err(ParseError::new(
                        ParseErrorKind::Custom("unterminated raw string literal".to_string()),
                        self.position(),
                    ));
                }
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range,
            value: eterned::BaseCoword::new(content),
        }))
    }

    pub fn interpolated_string_literal(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Consume 's!'
        self.advance(); // 's'
        self.advance(); // '!'

        self.expect_char('"')?;

        let mut parts = Vec::new();
        let mut current_str = String::new();

        while let Some(ch) = self.peek() {
            match ch {
                '"' => {
                    self.advance();
                    if !current_str.is_empty() {
                        let range = self.input().range_from(start);
                        parts.push(Syntax::Atom(lean_syn_expr::SyntaxAtom {
                            range,
                            value: eterned::BaseCoword::new(current_str),
                        }));
                    }
                    break;
                }
                '{' => {
                    // Save current string part if any
                    if !current_str.is_empty() {
                        let range = self.input().range_from(start);
                        parts.push(Syntax::Atom(lean_syn_expr::SyntaxAtom {
                            range,
                            value: eterned::BaseCoword::new(current_str.clone()),
                        }));
                        current_str.clear();
                    }

                    self.advance(); // consume '{'
                    self.skip_whitespace();

                    // Parse the interpolated expression
                    let expr = self.term()?;
                    parts.push(expr);

                    self.skip_whitespace();
                    self.expect_char('}')?;
                }
                '\\' => {
                    self.advance();
                    match self.peek() {
                        Some('n') => {
                            self.advance();
                            current_str.push('\n');
                        }
                        Some('t') => {
                            self.advance();
                            current_str.push('\t');
                        }
                        Some('r') => {
                            self.advance();
                            current_str.push('\r');
                        }
                        Some('\\') => {
                            self.advance();
                            current_str.push('\\');
                        }
                        Some('"') => {
                            self.advance();
                            current_str.push('"');
                        }
                        Some('{') => {
                            self.advance();
                            current_str.push('{');
                        }
                        Some('}') => {
                            self.advance();
                            current_str.push('}');
                        }
                        _ => {
                            return Err(ParseError::new(
                                ParseErrorKind::Custom("invalid escape sequence".to_string()),
                                self.position(),
                            ));
                        }
                    }
                }
                _ => {
                    current_str.push(ch);
                    self.advance();
                }
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
            kind: lean_syn_expr::SyntaxKind::StringInterpolation,
            range,
            children: parts.into(),
        })))
    }

    pub fn peek_raw_string(&self) -> bool {
        self.peek() == Some('r')
            && (self.input.peek_nth(1) == Some('"') || self.input.peek_nth(1) == Some('#'))
    }

    pub fn peek_interpolated_string(&self) -> bool {
        self.peek() == Some('s')
            && self.input.peek_nth(1) == Some('!')
            && self.input.peek_nth(2) == Some('"')
    }

    pub fn peek_special_number(&self) -> bool {
        if self.peek() != Some('0') {
            return false;
        }

        match self.input.peek_nth(1) {
            Some('x') | Some('X') => true, // hex
            Some('b') | Some('B') => true, // binary
            Some('o') | Some('O') => true, // octal
            _ => false,
        }
    }

    /// Parse a binder group: `(x y : α)` or `{α : Type}` or `[inst : Functor
    /// F]`
    pub fn binder_group(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let (_open_delim, close_delim, binder_kind) = match self.peek() {
            Some('(') => ('(', ')', lean_syn_expr::SyntaxKind::LeftParen),
            Some('{') => ('{', '}', lean_syn_expr::SyntaxKind::LeftBrace),
            Some('[') => ('[', ']', lean_syn_expr::SyntaxKind::LeftBracket),
            _ => {
                return Err(ParseError::new(
                    ParseErrorKind::Expected("binder".to_string()),
                    start,
                ))
            }
        };

        self.advance(); // consume opening delimiter
        self.skip_whitespace();

        let mut names = Vec::new();

        // Parse names
        while self.peek().is_some_and(is_id_start) {
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
