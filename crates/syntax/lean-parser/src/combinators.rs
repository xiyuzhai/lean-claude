use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
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
                        ParseErrorKind::Expected(format!("'{sep}' or '{close}'")),
                        self.position(),
                    ));
                }
            }
        }

        self.expect_char(close)?;
        Ok(items)
    }
}
