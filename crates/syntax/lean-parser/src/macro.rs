//! Macro and notation parsing for Lean 4

use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse a macro definition: `macro "name" : category => body`
    pub fn macro_def(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("macro")?;
        self.skip_whitespace();

        // Optional attributes
        let mut attributes = Vec::new();
        if self.peek() == Some('[') {
            attributes.push(self.parse_attributes()?);
            self.skip_whitespace();
        }

        // Optional precedence
        let precedence = if self.peek_keyword("(") {
            Some(self.parse_precedence_annotation()?)
        } else {
            None
        };
        self.skip_whitespace();

        // Optional name (for named macros)
        let name = if self.peek() == Some('"') {
            // String literal for syntax patterns
            Some(self.string_literal()?)
        } else if self.peek_keyword("atomic") || self.peek_keyword("leading") {
            // Macro kind specifier
            Some(self.identifier()?)
        } else if self.peek().is_some_and(|c| c.is_alphabetic()) {
            // Named macro
            Some(self.identifier()?)
        } else {
            None
        };
        self.skip_whitespace();

        // Parse pattern
        let pattern = if name.is_some() && self.peek() == Some(':') {
            // Category specification
            self.advance(); // consume ':'
            self.skip_whitespace();
            self.identifier()? // category name
        } else {
            // Direct pattern
            self.parse_macro_pattern()?
        };
        self.skip_whitespace();

        // Arrow
        if self.peek() == Some('=') && self.input().peek_nth(1) == Some('>') {
            self.advance(); // =
            self.advance(); // >
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("=>".to_string()),
                self.position(),
            ));
        }
        self.skip_whitespace();

        // Body
        let body = self.parse_macro_body()?;

        let range = self.input().range_from(start);
        let mut children = attributes;
        if let Some(prec) = precedence {
            children.push(prec);
        }
        if let Some(n) = name {
            children.push(n);
        }
        children.push(pattern);
        children.push(body);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::MacroDef,
            range,
            children: children.into(),
        })))
    }

    /// Parse macro_rules: `macro_rules | pattern => body | pattern => body`
    pub fn macro_rules(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("macro_rules")?;
        self.skip_whitespace();

        let mut rules = Vec::new();

        // Parse rules separated by |
        loop {
            if self.peek() == Some('|') {
                self.advance();
                self.skip_whitespace();
            }

            // Pattern
            let pattern = self.parse_macro_pattern()?;
            self.skip_whitespace();

            // Arrow
            self.expect_char('=')?;
            self.expect_char('>')?;
            self.skip_whitespace();

            // Body
            let body = self.parse_macro_body()?;

            rules.push(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::MacroRule,
                range: self.input().range_from(start),
                children: smallvec![pattern, body],
            })));

            self.skip_whitespace();
            if self.peek() != Some('|') {
                break;
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::MacroRules,
            range,
            children: rules.into(),
        })))
    }

    /// Parse a syntax declaration: `syntax "pattern" : category`
    pub fn syntax_def(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("syntax")?;
        self.skip_whitespace();

        // Optional attributes
        let mut children = Vec::new();
        if self.peek() == Some('[') {
            children.push(self.parse_attributes()?);
            self.skip_whitespace();
        }

        // Optional precedence
        if self.peek_keyword("(") {
            children.push(self.parse_precedence_annotation()?);
            self.skip_whitespace();
        }

        // Pattern or name
        let pattern = if self.peek() == Some('"') {
            self.string_literal()?
        } else {
            self.identifier()?
        };
        children.push(pattern);
        self.skip_whitespace();

        // Category
        self.expect_char(':')?;
        self.skip_whitespace();
        let category = self.identifier()?;
        children.push(category);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Syntax,
            range,
            children: children.into(),
        })))
    }

    /// Parse notation: `notation "pattern" => body`
    pub fn notation_def(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("notation")?;
        self.skip_whitespace();

        // Optional attributes and precedence
        let mut children = Vec::new();
        if self.peek() == Some('[') {
            children.push(self.parse_attributes()?);
            self.skip_whitespace();
        }

        if self.peek() == Some('(') {
            children.push(self.parse_precedence_annotation()?);
            self.skip_whitespace();
        }

        // Pattern
        let pattern = self.string_literal()?;
        children.push(pattern);
        self.skip_whitespace();

        // Arrow
        self.expect_char('=')?;
        self.expect_char('>')?;
        self.skip_whitespace();

        // Body
        let body = self.term()?;
        children.push(body);

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::NotationDef,
            range,
            children: children.into(),
        })))
    }

    /// Parse attributes: `[attr1, attr2]` or `@[attr1, attr2]`
    pub fn parse_attributes(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Optional @
        if self.peek() == Some('@') {
            self.advance();
        }

        self.expect_char('[')?;
        self.skip_whitespace();

        let mut attrs = Vec::new();

        while self.peek() != Some(']') {
            attrs.push(self.parse_attribute()?);
            self.skip_whitespace();

            if self.peek() == Some(',') {
                self.advance();
                self.skip_whitespace();
            } else if self.peek() != Some(']') {
                return Err(ParseError::boxed(
                    ParseErrorKind::Expected(", or ]".to_string()),
                    self.position(),
                ));
            }
        }

        self.expect_char(']')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::AttributeList,
            range,
            children: attrs.into(),
        })))
    }

    /// Parse a single attribute
    fn parse_attribute(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let name = self.identifier()?;
        let mut children = vec![name];

        // Optional attribute arguments
        if self.peek() == Some('(') {
            self.advance();
            self.skip_whitespace();

            while self.peek() != Some(')') {
                children.push(self.term()?);
                self.skip_whitespace();

                if self.peek() == Some(',') {
                    self.advance();
                    self.skip_whitespace();
                }
            }

            self.expect_char(')')?;
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Attribute,
            range,
            children: children.into(),
        })))
    }

    /// Parse precedence annotation: `(priority := 1000)`
    fn parse_precedence_annotation(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('(')?;
        self.skip_whitespace();

        let keyword = self.identifier()?; // "priority" or "prec"
        self.skip_whitespace();

        self.expect_char(':')?;
        self.expect_char('=')?;
        self.skip_whitespace();

        let value = self.number()?;
        self.skip_whitespace();

        self.expect_char(')')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Precedence,
            range,
            children: smallvec![keyword, value],
        })))
    }

    /// Parse a macro pattern
    fn parse_macro_pattern(&mut self) -> ParserResult<Syntax> {
        // For now, parse as a term
        // In a full implementation, this would handle special macro pattern syntax
        self.term()
    }

    /// Parse a macro body
    fn parse_macro_body(&mut self) -> ParserResult<Syntax> {
        // Check for do notation
        if self.peek_keyword("do") {
            self.parse_do_block()
        } else if self.peek() == Some('`') && self.input().peek_nth(1) == Some('(') {
            // Syntax quotation
            self.parse_syntax_quotation()
        } else {
            self.term()
        }
    }

    /// Parse a do block: `do statements...`
    fn parse_do_block(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("do")?;
        self.skip_whitespace();

        let mut statements = Vec::new();

        // Parse statements in the do block
        while !self.at_block_end() {
            if self.peek_keyword("let") {
                statements.push(self.parse_do_let()?);
            } else if self.peek_keyword("for") {
                statements.push(self.parse_do_for()?);
            } else if self.peek_keyword("try") {
                statements.push(self.parse_do_try()?);
            } else if self.peek_keyword("if") {
                statements.push(self.parse_do_if()?);
            } else {
                // Expression statement
                statements.push(self.term()?);
            }

            self.skip_whitespace();

            // Check for semicolon or newline
            if self.peek() == Some(';') {
                self.advance();
                self.skip_whitespace();
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::By, // Reuse By for do blocks for now
            range,
            children: statements.into(),
        })))
    }

    /// Parse do-let: `let pat := expr`
    fn parse_do_let(&mut self) -> ParserResult<Syntax> {
        self.let_term()
    }

    /// Parse do-for: `for x in xs do body`
    fn parse_do_for(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("for")?;
        self.skip_whitespace();

        let pat = self.pattern()?;
        self.skip_whitespace();

        self.keyword("in")?;
        self.skip_whitespace();

        let expr = self.term()?;
        self.skip_whitespace();

        self.keyword("do")?;
        self.skip_whitespace();

        let body = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Let, // Reuse Let for for loops for now
            range,
            children: smallvec![pat, expr, body],
        })))
    }

    /// Parse do-try: `try expr catch pat => handler`
    fn parse_do_try(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("try")?;
        self.skip_whitespace();

        let expr = self.term()?;
        self.skip_whitespace();

        self.keyword("catch")?;
        self.skip_whitespace();

        let pat = self.pattern()?;
        self.skip_whitespace();

        self.expect_char('=')?;
        self.expect_char('>')?;
        self.skip_whitespace();

        let handler = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Match, // Reuse Match for try-catch for now
            range,
            children: smallvec![expr, pat, handler],
        })))
    }

    /// Parse do-if: `if cond then expr else expr`
    fn parse_do_if(&mut self) -> ParserResult<Syntax> {
        self.if_term()
    }

    /// Check if we're at the end of a block
    fn at_block_end(&self) -> bool {
        matches!(
            self.peek(),
            None | Some('|') | Some(')') | Some('}') | Some(']')
        ) || self.peek_keyword("where")
            || self.peek_keyword("end")
            || self.peek_keyword("else")
            || self.peek_keyword("catch")
    }

    /// Parse syntax quotation: `` `(pattern) `` or `` `(category| pattern) ``
    pub fn parse_syntax_quotation(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('`')?;
        self.expect_char('(')?;
        self.skip_whitespace();

        let mut children = Vec::new();

        // Check for category specification
        let category = if self.peek().is_some_and(|c| c.is_alphabetic()) {
            self.try_parse(|p| {
                let id = p.identifier()?;
                p.skip_whitespace();
                if p.peek() == Some('|') {
                    p.advance(); // consume '|'
                    p.skip_whitespace();
                    Ok(id)
                } else {
                    Err(ParseError::boxed(
                        ParseErrorKind::Expected("|".to_string()),
                        p.position(),
                    ))
                }
            })
            .ok()
        } else {
            None
        };

        if let Some(cat) = category {
            children.push(cat);
        }

        // Parse the quoted syntax
        while self.peek() != Some(')') {
            if self.peek() == Some('$') {
                // Antiquotation
                children.push(self.parse_antiquotation()?);
            } else {
                // Regular syntax element - parse based on context
                let elem = self.parse_quotation_element()?;
                children.push(elem);
            }
            self.skip_whitespace();

            // Handle comma-separated elements
            if self.peek() == Some(',') {
                self.advance();
                self.skip_whitespace();
            }
        }

        self.expect_char(')')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::SyntaxQuotation,
            range,
            children: children.into(),
        })))
    }

    /// Parse an element inside a quotation
    fn parse_quotation_element(&mut self) -> ParserResult<Syntax> {
        // Inside quotations, we need to be more careful about parsing
        // to handle various syntax forms
        match self.peek() {
            Some('∀') | Some('λ') | Some('\\') => self.term(),
            Some('(') | Some('{') | Some('[') => self.term(),
            Some(ch) if ch.is_alphabetic() => {
                // Could be a keyword or identifier
                if self.peek_keyword("fun")
                    || self.peek_keyword("match")
                    || self.peek_keyword("let")
                    || self.peek_keyword("have")
                {
                    self.term()
                } else {
                    // Parse as application or identifier
                    self.term()
                }
            }
            _ => self.term(),
        }
    }

    /// Parse antiquotation: `$name`, `$(expr)`, `$name:category`, or splice
    /// `$xs,*`
    fn parse_antiquotation(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('$')?;

        let mut children = Vec::new();

        // Parse the antiquoted element
        let content = if self.peek() == Some('(') {
            self.advance();
            self.skip_whitespace();
            let expr = self.term()?;
            self.skip_whitespace();
            self.expect_char(')')?;
            expr
        } else {
            let id = self.identifier()?;

            // Check for category annotation
            if self.peek() == Some(':') {
                children.push(id);
                self.advance(); // consume ':'
                self.skip_whitespace();
                let category = self.identifier()?;
                children.push(category);

                // Create a node with category
                let range = self.input().range_from(start);
                return Ok(Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::SyntaxAntiquotation,
                    range,
                    children: children.into(),
                })));
            }

            id
        };

        children.push(content);

        // Check for splice notation (,*)
        if self.peek() == Some(',') && self.input().peek_nth(1) == Some('*') {
            self.advance(); // consume ','
            self.advance(); // consume '*'

            // Add a marker for splice
            let splice_start = self.position();
            let splice_range = self.input().range_from(splice_start);
            children.push(Syntax::Atom(lean_syn_expr::SyntaxAtom {
                range: splice_range,
                value: eterned::BaseCoword::new(",*"),
            }));
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::SyntaxAntiquotation,
            range,
            children: children.into(),
        })))
    }
}
