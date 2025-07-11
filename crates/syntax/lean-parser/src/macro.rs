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
        let (name, is_string_pattern) = if self.peek() == Some('"') {
            // String literal for syntax patterns
            (Some(self.string_literal()?), true)
        } else if self.peek_keyword("atomic") || self.peek_keyword("leading") {
            // Macro kind specifier
            (Some(self.identifier()?), false)
        } else if self.peek().is_some_and(|c| c.is_alphabetic()) {
            // Named macro
            (Some(self.identifier()?), false)
        } else {
            (None, false)
        };
        self.skip_whitespace();

        // Parse pattern and category
        let (pattern, category, name_used_as_pattern) = if let Some(ref n) = name {
            // Check if this is a string literal name
            if is_string_pattern {
                // For string literal macros, check if we have a pattern or go directly to
                // category
                if self.peek() == Some(':') {
                    // No pattern, just category
                    self.advance(); // consume ':'
                    self.skip_whitespace();
                    let cat = Some(self.identifier()?);
                    (n.clone(), cat, true) // Use the string literal as the
                                           // pattern
                } else {
                    // Has pattern parameters after the string
                    let pat = self.parse_macro_pattern()?;
                    self.skip_whitespace();

                    // Then category after colon
                    let cat = if self.peek() == Some(':') {
                        self.advance(); // consume ':'
                        self.skip_whitespace();
                        Some(self.identifier()?)
                    } else {
                        None
                    };

                    // Just use the pattern, don't combine with the name
                    (pat, cat, false)
                }
            } else {
                // Regular named macro
                let pat = self.parse_macro_pattern()?;
                self.skip_whitespace();

                // Then category after colon
                let cat = if self.peek() == Some(':') {
                    self.advance(); // consume ':'
                    self.skip_whitespace();
                    Some(self.identifier()?)
                } else {
                    None
                };
                (pat, cat, false)
            }
        } else {
            // Anonymous macro - parse pattern directly
            (self.parse_macro_pattern()?, None, false)
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

        // Only add name if it wasn't used as the pattern itself
        if let Some(n) = name {
            if !name_used_as_pattern {
                children.push(n);
            }
        }
        children.push(pattern);
        if let Some(cat) = category {
            children.push(cat);
        }
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
    pub fn parse_precedence_annotation(&mut self) -> ParserResult<Syntax> {
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

    /// Parse a macro pattern (e.g., x:term or multiple parameters with
    /// literals)
    fn parse_macro_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Check if this is a syntax quotation (for macro_rules)
        if self.peek() == Some('`') && self.input().peek_nth(1) == Some('(') {
            return self.parse_syntax_quotation_impl(true); // true = is_pattern
        }

        // Parse a pattern that can contain typed parameters and string literals
        let mut elements = Vec::new();

        // Parse pattern elements
        loop {
            self.skip_whitespace();

            // Check for string literal
            if self.peek() == Some('"') {
                elements.push(self.string_literal()?);
                self.skip_whitespace();
                continue;
            }

            // Check for typed parameter
            if self.peek().is_some_and(|c| c.is_alphabetic()) {
                // Try to parse a typed parameter (with optional * for repetition)
                if let Ok(typed_param) = self.try_parse(|p| {
                    let ident = p.identifier()?;
                    p.skip_whitespace();

                    if p.peek() == Some(':') {
                        // This is a typed parameter
                        p.advance(); // consume ':'
                        let category = p.identifier()?;

                        // Check for repetition operator *
                        let mut is_repeated = false;
                        if p.peek() == Some('*') {
                            p.advance(); // consume '*'
                            is_repeated = true;
                        }

                        let range = p.input().range_from(start);
                        let mut param = Syntax::Node(Box::new(SyntaxNode {
                            kind: SyntaxKind::App, // Use App for typed param
                            range,
                            children: smallvec![ident, category],
                        }));

                        // If repeated, wrap in a repetition node
                        if is_repeated {
                            param = Syntax::Node(Box::new(SyntaxNode {
                                kind: SyntaxKind::App, // Use App for repetition
                                range,
                                children: smallvec![param],
                            }));
                        }

                        Ok(param)
                    } else {
                        Err(ParseError::boxed(
                            ParseErrorKind::Expected(":".to_string()),
                            p.position(),
                        ))
                    }
                }) {
                    elements.push(typed_param);
                    self.skip_whitespace();
                    continue;
                }
            }

            // No more pattern elements
            break;
        }

        // Create pattern node
        if elements.is_empty() {
            // Empty pattern - parse as term
            self.term()
        } else if elements.len() == 1 {
            // Single element
            Ok(elements.into_iter().next().unwrap())
        } else {
            // Multiple elements - create a pattern node
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::App, // Use App for pattern
                range,
                children: elements.into(),
            })))
        }
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
    pub(crate) fn at_block_end(&self) -> bool {
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
        self.parse_syntax_quotation_impl(false)
    }

    /// Parse syntax quotation with control over whether it's a pattern
    fn parse_syntax_quotation_impl(&mut self, is_pattern: bool) -> ParserResult<Syntax> {
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

        // Parse the quoted syntax as a single term
        // (antiquotations will be handled during term parsing)
        let quoted_term = if is_pattern {
            self.parse_quotation_pattern()?
        } else {
            self.parse_quotation_term()?
        };
        children.push(quoted_term);

        self.expect_char(')')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::SyntaxQuotation,
            range,
            children: children.into(),
        })))
    }

    /// Parse a term inside a quotation (may contain antiquotations)
    fn parse_quotation_term(&mut self) -> ParserResult<Syntax> {
        // Parse a proper term that may contain antiquotations
        // This should handle applications, operators, etc. properly
        self.parse_quotation_term_with_app()
    }

    /// Parse a term inside quotation with proper application handling
    fn parse_quotation_term_with_app(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Parse the first element (could be function or atom)
        let mut result = self.parse_quotation_atom()?;

        // Keep parsing arguments while we have them
        loop {
            self.skip_whitespace();

            // Check if we have another argument
            if self.peek() == Some(')')  // End of quotation
                || self.peek() == Some(',')  // List separator
                || self.peek() == Some(']')  // End of list
                || self.input().is_at_end()
            {
                break;
            }

            // Check for operators
            if let Some(ch) = self.peek() {
                // Check for ++ operator first
                if ch == '+' && self.input().peek_nth(1) == Some('+') {
                    // ++ operator
                    let op_start = self.position();
                    self.advance(); // consume first +
                    self.advance(); // consume second +
                    let op_range = self.input().range_from(op_start);
                    let op_syntax = Syntax::Atom(lean_syn_expr::SyntaxAtom {
                        range: op_range,
                        value: eterned::BaseCoword::new("++".to_string()),
                    });

                    self.skip_whitespace();
                    let right = self.parse_quotation_term_with_app()?;

                    let range = self.input().range_from(start);
                    result = Syntax::Node(Box::new(SyntaxNode {
                        kind: SyntaxKind::BinOp,
                        range,
                        children: smallvec![result, op_syntax, right],
                    }));
                    break;
                } else if "+-*/".contains(ch) {
                    // Single character binary operator
                    let op_start = self.position();
                    let op = self.advance().unwrap();
                    let op_range = self.input().range_from(op_start);
                    let op_syntax = Syntax::Atom(lean_syn_expr::SyntaxAtom {
                        range: op_range,
                        value: eterned::BaseCoword::new(op.to_string()),
                    });

                    self.skip_whitespace();
                    let right = self.parse_quotation_term_with_app()?;

                    let range = self.input().range_from(start);
                    result = Syntax::Node(Box::new(SyntaxNode {
                        kind: SyntaxKind::BinOp,
                        range,
                        children: smallvec![result, op_syntax, right],
                    }));
                    break;
                }
            }

            // Try to parse another argument
            if let Ok(arg) = self.try_parse(|p| p.parse_quotation_atom()) {
                // Create application node
                let range = self.input().range_from(start);
                result = Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::App,
                    range,
                    children: smallvec![result, arg],
                }));
            } else {
                break;
            }
        }

        Ok(result)
    }

    /// Parse an atomic term in a quotation
    fn parse_quotation_atom(&mut self) -> ParserResult<Syntax> {
        self.skip_whitespace();

        if self.peek() == Some('$') {
            // Antiquotation
            self.parse_antiquotation()
        } else if self.peek() == Some('(') {
            // Parenthesized term in quotation context
            self.parse_quotation_paren()
        } else if self.peek() == Some('[') {
            // List pattern
            self.parse_list_pattern()
        } else if self.peek().is_some_and(|c| c.is_numeric()) {
            // Number
            self.number()
        } else if self.peek_keyword("fun") || self.peek() == Some('λ') {
            // Parse lambda
            self.parse_quotation_lambda()
        } else if self.peek_keyword("let") {
            // Parse let expression
            self.parse_quotation_let()
        } else if self.peek().is_some_and(|c| c.is_alphabetic() || c == '_') {
            // Just parse as identifier - this handles both regular identifiers
            // and custom syntax like "myif"
            self.parse_qualified_identifier()
        } else {
            Err(ParseError::boxed(
                ParseErrorKind::Expected("quotation term".to_string()),
                self.position(),
            ))
        }
    }

    /// Parse parenthesized term in quotation context
    fn parse_quotation_paren(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        self.expect_char('(')?;
        self.skip_whitespace();

        // Check for unit value ()
        if self.peek() == Some(')') {
            self.advance(); // consume ')'
            let range = self.input().range_from(start);
            return Ok(Syntax::Atom(lean_syn_expr::SyntaxAtom {
                range,
                value: eterned::BaseCoword::new("Unit.unit"),
            }));
        }

        // Parse the content using quotation parser
        let term = self.parse_quotation_term_with_app()?;
        self.skip_whitespace();
        self.expect_char(')')?;
        Ok(term)
    }

    /// Parse a potentially qualified identifier (e.g., List.nil)
    fn parse_qualified_identifier(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut parts = vec![self.identifier()?];

        // Check for qualification dots
        while self.peek() == Some('.')
            && self.input().peek_nth(1).is_some_and(|c| c.is_alphabetic())
        {
            self.advance(); // consume '.'
            parts.push(self.identifier()?);
        }

        if parts.len() == 1 {
            Ok(parts.into_iter().next().unwrap())
        } else {
            // Create a qualified name node using App
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::App,
                range,
                children: parts.into(),
            })))
        }
    }

    /// Parse antiquotation: `$name`, `$(expr)`, `$name:category`, or splice
    /// `$xs,*`
    pub fn parse_antiquotation(&mut self) -> ParserResult<Syntax> {
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

            // Create a splice node instead of antiquotation
            let range = self.input().range_from(start);
            return Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::SyntaxSplice,
                range,
                children: children.into(),
            })));
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::SyntaxAntiquotation,
            range,
            children: children.into(),
        })))
    }

    /// Parse lambda inside quotation: fun x => body
    fn parse_quotation_lambda(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Consume 'fun' or 'λ'
        if self.peek_keyword("fun") {
            self.keyword("fun")?;
        } else {
            self.advance(); // consume λ
        }

        self.skip_whitespace();

        // Parse binder
        let binder = self.identifier()?;

        self.skip_whitespace();

        // Expect =>
        self.expect_char('=')?;
        self.expect_char('>')?;

        self.skip_whitespace();

        // Parse body
        let body = self.parse_quotation_term_with_app()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Lambda,
            range,
            children: smallvec![binder, body],
        })))
    }

    /// Parse let expression inside quotation: let x := val; body
    fn parse_quotation_let(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("let")?;
        self.skip_whitespace();

        // Parse binder
        let binder = self.identifier()?;
        self.skip_whitespace();

        // Expect :=
        self.expect_char(':')?;
        self.expect_char('=')?;
        self.skip_whitespace();

        // Parse value
        let value = self.parse_quotation_term_with_app()?;
        self.skip_whitespace();

        // Expect semicolon
        self.expect_char(';')?;
        self.skip_whitespace();

        // Parse body
        let body = self.parse_quotation_term_with_app()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Let,
            range,
            children: smallvec![binder, value, body],
        })))
    }

    /// Parse if-then-else inside quotation
    #[allow(dead_code)]
    fn parse_quotation_if(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("if")?;
        self.skip_whitespace();

        // Parse condition
        let cond = self.parse_quotation_term_with_app()?;

        self.skip_whitespace();
        self.keyword("then")?;
        self.skip_whitespace();

        // Parse then branch
        let then_branch = self.parse_quotation_term_with_app()?;

        self.skip_whitespace();
        self.keyword("else")?;
        self.skip_whitespace();

        // Parse else branch
        let else_branch = self.parse_quotation_term_with_app()?;

        let range = self.input().range_from(start);

        // Create an if-then-else as a function application
        // if c then t else e => (((if c) then t) else e)
        let if_atom = Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range: self.input().range_from(start),
            value: eterned::BaseCoword::new("if".to_string()),
        });

        let then_atom = Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range: self.input().range_from(start),
            value: eterned::BaseCoword::new("then".to_string()),
        });

        let else_atom = Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range: self.input().range_from(start),
            value: eterned::BaseCoword::new("else".to_string()),
        });

        // Build nested applications
        let if_cond = Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::App,
            range,
            children: smallvec![if_atom, cond],
        }));

        let if_cond_then = Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::App,
            range,
            children: smallvec![if_cond, then_atom],
        }));

        let if_cond_then_branch = Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::App,
            range,
            children: smallvec![if_cond_then, then_branch],
        }));

        let if_cond_then_branch_else = Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::App,
            range,
            children: smallvec![if_cond_then_branch, else_atom],
        }));

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::App,
            range,
            children: smallvec![if_cond_then_branch_else, else_branch],
        })))
    }

    /// Parse a list pattern: [elem1, elem2, ..., $xs,*]
    fn parse_list_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.expect_char('[')?;
        self.skip_whitespace();

        let mut elements = Vec::new();

        // Parse list elements
        while self.peek() != Some(']') && !self.input().is_at_end() {
            // Parse element (could be antiquotation or regular term)
            if self.peek() == Some('$') {
                elements.push(self.parse_antiquotation()?);
            } else {
                // Parse a simple term element

                // For now, just parse identifiers and numbers as list elements
                if self.peek().is_some_and(|c| c.is_numeric()) {
                    elements.push(self.number()?);
                } else if self.peek().is_some_and(|c| c.is_alphabetic()) {
                    elements.push(self.identifier()?);
                } else if self.peek() == Some('(') {
                    elements.push(self.paren_term()?);
                } else if self.peek() == Some('[') {
                    // Nested list
                    elements.push(self.parse_list_pattern()?);
                } else {
                    return Err(ParseError::boxed(
                        ParseErrorKind::Expected("list element".to_string()),
                        self.position(),
                    ));
                }
            }

            self.skip_whitespace();

            // Check for comma separator
            if self.peek() == Some(',') {
                self.advance();
                self.skip_whitespace();

                // If we see ']' after comma, it's a trailing comma
                if self.peek() == Some(']') {
                    break;
                }
            } else if self.peek() != Some(']') {
                // No comma and not at end - error
                return Err(ParseError::boxed(
                    ParseErrorKind::Expected("',' or ']'".to_string()),
                    self.position(),
                ));
            }
        }

        self.expect_char(']')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::List,
            range,
            children: elements.into(),
        })))
    }

    /// Parse a pattern inside a quotation (for macro_rules patterns)
    /// This is like parse_quotation_term but treats keywords as regular
    /// identifiers
    fn parse_quotation_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        // Parse tokens until we hit the closing paren
        let mut tokens = Vec::new();

        while self.peek() != Some(')') && !self.input().is_at_end() {
            self.skip_whitespace();

            if self.peek() == Some(')') {
                break;
            }

            // Parse one token
            if self.peek() == Some('$') {
                // Antiquotation
                tokens.push(self.parse_antiquotation()?);
            } else if self.peek() == Some('(') {
                // Nested parens
                tokens.push(self.parse_quotation_paren()?);
            } else if self.peek() == Some('[') {
                // List
                tokens.push(self.parse_list_pattern()?);
            } else if self.peek().is_some_and(|c| c.is_numeric()) {
                // Number
                tokens.push(self.number()?);
            } else if self.peek().is_some_and(|c| c.is_alphabetic() || c == '_') {
                // Identifier (including keywords)
                tokens.push(self.identifier()?);
            } else {
                // Single character token
                if let Some(ch) = self.advance() {
                    let range = self.input().range_from(self.position());
                    tokens.push(Syntax::Atom(lean_syn_expr::SyntaxAtom {
                        range,
                        value: eterned::BaseCoword::new(ch.to_string()),
                    }));
                }
            }
        }

        // If we have multiple tokens, wrap them in an App node
        if tokens.is_empty() {
            Err(ParseError::boxed(
                ParseErrorKind::Expected("pattern content".to_string()),
                start,
            ))
        } else if tokens.len() == 1 {
            Ok(tokens.into_iter().next().unwrap())
        } else {
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::App,
                range,
                children: tokens.into(),
            })))
        }
    }

    /// Parse match expressions inside quotations
    #[allow(dead_code)]
    fn parse_quotation_match(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("match")?;
        self.skip_whitespace();

        // Parse scrutinee
        let scrutinee = self.parse_quotation_atom()?; // Changed from parse_quotation_term
        self.skip_whitespace();

        // Expect 'with'
        self.keyword("with")?;
        self.skip_whitespace();

        // Parse arms
        let mut arms = Vec::new();

        loop {
            // Optional leading |
            if self.peek() == Some('|') {
                self.advance();
                self.skip_whitespace();
            }

            // Parse pattern (for now, just parse as term)
            let pattern = self.parse_quotation_atom()?;
            self.skip_whitespace();

            // Expect =>
            self.expect_char('=')?;
            self.expect_char('>')?;
            self.skip_whitespace();

            // Parse body
            let body = self.parse_quotation_atom()?;

            // Create arm node
            let arm_range = self.input().range_from(start);
            let arm = Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::MatchArm,
                range: arm_range,
                children: smallvec![pattern, body],
            }));
            arms.push(arm);

            self.skip_whitespace();

            // Check if there's another arm
            if self.peek() != Some('|') {
                break;
            }
        }

        let range = self.input().range_from(start);
        let mut children = smallvec![scrutinee];
        children.extend(arms);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Match,
            range,
            children,
        })))
    }
}
