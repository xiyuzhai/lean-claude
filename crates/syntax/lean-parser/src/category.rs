//! Parser category system inspired by Lean 4's extensible parsing
//! with Rust-style error handling and recovery

use std::collections::HashMap;

use lean_syn_expr::Syntax;

use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserFn, ParserResult},
    precedence::Precedence,
};

/// Leading identifier behavior for a parser category
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LeadingIdentBehavior {
    /// Only accept registered keywords
    Keyword,
    /// Accept any identifier
    Ident,
    /// Accept both keywords and identifiers
    Both,
}

/// A parser function with metadata for error recovery
#[derive(Clone)]
pub struct ParserEntry {
    /// The parser function
    pub parser: ParserFn,
    /// Precedence for Pratt parsing
    pub precedence: Precedence,
    /// Human-readable name for error messages
    pub name: String,
    /// Example usage for error suggestions
    pub example: Option<String>,
    /// Help text for when this parser fails
    pub help: Option<String>,
}

/// Parsing table for a category
#[derive(Clone, Default)]
pub struct ParsingTable {
    /// Leading parsers indexed by first token
    pub leading: HashMap<String, Vec<ParserEntry>>,
    /// Trailing parsers (operators) with precedence
    pub trailing: HashMap<String, ParserEntry>,
    /// Default parsers to try when no specific match
    pub default_parsers: Vec<ParserEntry>,
}

impl ParsingTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a leading parser (triggered by specific token)
    pub fn add_leading(&mut self, trigger: impl Into<String>, entry: ParserEntry) {
        self.leading.entry(trigger.into()).or_default().push(entry);
    }

    /// Add a trailing parser (operator)
    pub fn add_trailing(&mut self, operator: impl Into<String>, entry: ParserEntry) {
        self.trailing.insert(operator.into(), entry);
    }

    /// Add a default parser
    pub fn add_default(&mut self, entry: ParserEntry) {
        self.default_parsers.push(entry);
    }
}

/// A parser category (term, tactic, command, etc.)
#[derive(Clone)]
pub struct ParserCategory {
    /// Name of the category
    pub name: String,
    /// Parsing tables
    pub tables: ParsingTable,
    /// How to handle leading identifiers
    pub behavior: LeadingIdentBehavior,
    /// Error recovery strategies
    pub recovery_hints: Vec<RecoveryHint>,
}

/// Hints for error recovery and better error messages
#[derive(Clone)]
pub struct RecoveryHint {
    /// When we see this token...
    pub when_seeing: String,
    /// ...but expected something else, suggest this
    pub suggest: String,
    /// Additional help text
    pub help: Option<String>,
    /// Example of correct usage
    pub example: Option<String>,
}

impl ParserCategory {
    pub fn new(name: impl Into<String>, behavior: LeadingIdentBehavior) -> Self {
        Self {
            name: name.into(),
            tables: ParsingTable::new(),
            behavior,
            recovery_hints: Vec::new(),
        }
    }

    /// Add a recovery hint for better error messages
    pub fn add_recovery_hint(&mut self, hint: RecoveryHint) {
        self.recovery_hints.push(hint);
    }

    /// Parse with this category's rules
    pub fn parse<'a>(&self, parser: &mut Parser<'a>, min_prec: Precedence) -> ParserResult<Syntax> {
        self.parse_with_recovery(parser, min_prec)
    }

    /// Parse with error recovery and enhanced error messages
    fn parse_with_recovery<'a>(
        &self,
        parser: &mut Parser<'a>,
        min_prec: Precedence,
    ) -> ParserResult<Syntax> {
        let start_pos = parser.position();

        // Try to parse with recovery
        match self.try_parse_internal(parser, min_prec) {
            Ok(syntax) => Ok(syntax),
            Err(err) => {
                // Enhance error with category-specific help
                let enhanced_error = self.enhance_error(parser, err, start_pos);

                // Try recovery strategies
                if let Some(recovered) = self.try_recovery(parser, &enhanced_error) {
                    // Add warning about recovery
                    parser.add_warning(
                        parser.input().range_from(start_pos),
                        format!("Recovered from syntax error in {}", self.name),
                    );
                    Ok(recovered)
                } else {
                    Err(enhanced_error)
                }
            }
        }
    }

    fn try_parse_internal<'a>(
        &self,
        parser: &mut Parser<'a>,
        min_prec: Precedence,
    ) -> ParserResult<Syntax> {
        parser.skip_whitespace();

        // Try leading parsers based on current token
        if let Some(token) = parser.peek() {
            let token_str = token.to_string();

            // Check for specific leading parser
            if let Some(entries) = self.tables.leading.get(&token_str) {
                for entry in entries {
                    if let Ok(result) = parser.try_parse(|p| (entry.parser)(p)) {
                        return self.continue_parsing(parser, result, min_prec);
                    }
                }
            }
        }

        // Try default parsers
        for entry in &self.tables.default_parsers {
            if let Ok(result) = parser.try_parse(|p| (entry.parser)(p)) {
                return self.continue_parsing(parser, result, min_prec);
            }
        }

        // Generate helpful error
        Err(Box::new(self.expected_error(parser)))
    }

    fn continue_parsing<'a>(
        &self,
        parser: &mut Parser<'a>,
        mut left: Syntax,
        min_prec: Precedence,
    ) -> ParserResult<Syntax> {
        loop {
            parser.skip_whitespace();

            // Check for trailing operators
            if let Some(op_entry) = self.peek_trailing_operator(parser) {
                if op_entry.precedence < min_prec {
                    break;
                }

                // Parse operator and right-hand side
                left = self.parse_trailing(parser, left, op_entry)?;
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn peek_trailing_operator<'a>(&self, parser: &Parser<'a>) -> Option<&ParserEntry> {
        // Check two-character operators first
        if let Some(ch1) = parser.peek() {
            if let Some(ch2) = parser.input().peek_nth(1) {
                let two_char = format!("{ch1}{ch2}");
                if let Some(entry) = self.tables.trailing.get(&two_char) {
                    return Some(entry);
                }
            }

            // Then single character
            let one_char = ch1.to_string();
            if let Some(entry) = self.tables.trailing.get(&one_char) {
                return Some(entry);
            }
        }

        None
    }

    fn parse_trailing<'a>(
        &self,
        parser: &mut Parser<'a>,
        left: Syntax,
        op_entry: &ParserEntry,
    ) -> ParserResult<Syntax> {
        let op_start = parser.position();

        // Consume the operator token(s)
        let op_str = if let Some(ch1) = parser.peek() {
            if let Some(ch2) = parser.input().peek_nth(1) {
                let two_char = format!("{ch1}{ch2}");
                if self.tables.trailing.contains_key(&two_char) {
                    parser.advance();
                    parser.advance();
                    two_char
                } else {
                    parser.advance();
                    ch1.to_string()
                }
            } else {
                parser.advance();
                ch1.to_string()
            }
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::UnexpectedEof,
                parser.position(),
            ));
        };

        let op_range = parser.input().range_from(op_start);

        // Create operator atom
        let op_atom = Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range: op_range,
            value: eterned::BaseCoword::new(op_str),
        });

        // Parse right-hand side with appropriate precedence
        let right_prec = match op_entry.precedence.associativity() {
            crate::precedence::Associativity::Left => op_entry.precedence.next(),
            crate::precedence::Associativity::Right => op_entry.precedence,
            crate::precedence::Associativity::None => op_entry.precedence.next(),
        };

        parser.skip_whitespace();
        let right = self.parse(parser, right_prec)?;

        // Create binary operator node
        let left_range = left.range().cloned().unwrap_or(lean_syn_expr::SourceRange {
            start: parser.position(),
            end: parser.position(),
        });
        let right_range = right
            .range()
            .cloned()
            .unwrap_or(lean_syn_expr::SourceRange {
                start: parser.position(),
                end: parser.position(),
            });
        let range = lean_syn_expr::SourceRange {
            start: left_range.start,
            end: right_range.end,
        };

        Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
            kind: lean_syn_expr::SyntaxKind::BinOp,
            range,
            children: vec![left, op_atom, right].into(),
        })))
    }

    fn enhance_error<'a>(
        &self,
        parser: &Parser<'a>,
        mut error: Box<ParseError>,
        _start_pos: lean_syn_expr::SourcePos,
    ) -> Box<ParseError> {
        // Add category context
        error.add_context(format!("while parsing {}", self.name));

        // Check recovery hints
        if let Some(token) = parser.peek() {
            let token_str = token.to_string();

            for hint in &self.recovery_hints {
                if hint.when_seeing == token_str {
                    error.add_suggestion(hint.suggest.clone());
                    if let Some(help) = &hint.help {
                        error.add_help(help.clone());
                    }
                    if let Some(example) = &hint.example {
                        error.add_example(example.clone());
                    }
                    break;
                }
            }
        }

        // Add available alternatives
        let mut expected = Vec::new();
        for token in self.tables.leading.keys() {
            expected.push(format!("'{token}'"));
        }
        if !expected.is_empty() {
            error.add_expected_list(expected);
        }

        error
    }

    fn try_recovery<'a>(&self, _parser: &mut Parser<'a>, _error: &ParseError) -> Option<Syntax> {
        // Implement various recovery strategies
        // For now, return None
        None
    }

    fn expected_error<'a>(&self, parser: &Parser<'a>) -> ParseError {
        let mut expected = Vec::new();

        // Collect what we could parse here
        for entries in self.tables.leading.values() {
            if let Some(entry) = entries.first() {
                expected.push(entry.name.clone());
            }
        }

        ParseError::new(ParseErrorKind::ExpectedOneOf(expected), parser.position())
    }
}

/// Category registry for managing all parser categories
#[derive(Default)]
pub struct CategoryRegistry {
    categories: HashMap<String, ParserCategory>,
}

impl CategoryRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a new category
    pub fn register(&mut self, category: ParserCategory) {
        self.categories.insert(category.name.clone(), category);
    }

    /// Get a category by name
    pub fn get(&self, name: &str) -> Option<&ParserCategory> {
        self.categories.get(name)
    }

    /// Get a mutable category by name
    pub fn get_mut(&mut self, name: &str) -> Option<&mut ParserCategory> {
        self.categories.get_mut(name)
    }
}

/// Initialize standard Lean categories
pub fn init_standard_categories() -> CategoryRegistry {
    use std::rc::Rc;

    let mut registry = CategoryRegistry::new();

    // Term category
    let mut term_category = ParserCategory::new("term", LeadingIdentBehavior::Both);

    // Add leading parsers for term category
    // Lambda expressions
    term_category.tables.add_leading(
        "λ",
        ParserEntry {
            parser: Rc::new(|p| p.lambda_term()),
            precedence: Precedence::MAX,
            name: "lambda expression".to_string(),
            example: Some("λ x => x + 1".to_string()),
            help: Some("Lambda expressions define anonymous functions".to_string()),
        },
    );

    term_category.tables.add_leading(
        "\\",
        ParserEntry {
            parser: Rc::new(|p| p.lambda_term()),
            precedence: Precedence::MAX,
            name: "lambda expression".to_string(),
            example: Some("\\x => x + 1".to_string()),
            help: Some("Backslash is an ASCII alternative to λ".to_string()),
        },
    );

    term_category.tables.add_leading(
        "fun",
        ParserEntry {
            parser: Rc::new(|p| p.lambda_term()),
            precedence: Precedence::MAX,
            name: "function".to_string(),
            example: Some("fun x => x + 1".to_string()),
            help: Some("'fun' keyword defines anonymous functions".to_string()),
        },
    );

    // Forall quantifier
    term_category.tables.add_leading(
        "∀",
        ParserEntry {
            parser: Rc::new(|p| p.forall_term()),
            precedence: Precedence::MAX,
            name: "universal quantifier".to_string(),
            example: Some("∀ x, P x".to_string()),
            help: Some("Universal quantification over a type".to_string()),
        },
    );

    term_category.tables.add_leading(
        "forall",
        ParserEntry {
            parser: Rc::new(|p| p.forall_term()),
            precedence: Precedence::MAX,
            name: "universal quantifier".to_string(),
            example: Some("forall x, P x".to_string()),
            help: Some("ASCII alternative to ∀".to_string()),
        },
    );

    // Let expressions
    term_category.tables.add_leading(
        "let",
        ParserEntry {
            parser: Rc::new(|p| p.let_term()),
            precedence: Precedence::MAX,
            name: "let expression".to_string(),
            example: Some("let x := 5 in x + 1".to_string()),
            help: Some("Local variable binding".to_string()),
        },
    );

    // Have expressions
    term_category.tables.add_leading(
        "have",
        ParserEntry {
            parser: Rc::new(|p| p.have_term()),
            precedence: Precedence::MAX,
            name: "have expression".to_string(),
            example: Some("have h : P := proof".to_string()),
            help: Some("Introduce a local proof".to_string()),
        },
    );

    // Show expressions
    term_category.tables.add_leading(
        "show",
        ParserEntry {
            parser: Rc::new(|p| p.show_term()),
            precedence: Precedence::MAX,
            name: "show expression".to_string(),
            example: Some("show P from proof".to_string()),
            help: Some("Explicitly state what is being proven".to_string()),
        },
    );

    // Calc expressions
    term_category.tables.add_leading(
        "calc",
        ParserEntry {
            parser: Rc::new(|p| p.calc_term()),
            precedence: Precedence::MAX,
            name: "calc expression".to_string(),
            example: Some("calc a = b := proof1\n     _ = c := proof2".to_string()),
            help: Some("Calculational proof".to_string()),
        },
    );

    // Match expressions
    term_category.tables.add_leading(
        "match",
        ParserEntry {
            parser: Rc::new(|p| p.match_expr()),
            precedence: Precedence::MAX,
            name: "match expression".to_string(),
            example: Some("match x with | some y => y | none => 0".to_string()),
            help: Some("Pattern matching on values".to_string()),
        },
    );

    // By tactic
    term_category.tables.add_leading(
        "by",
        ParserEntry {
            parser: Rc::new(|p| p.by_tactic()),
            precedence: Precedence::MAX,
            name: "tactic proof".to_string(),
            example: Some("by exact h".to_string()),
            help: Some("Switch to tactic mode for proving".to_string()),
        },
    );

    // Parentheses
    term_category.tables.add_leading(
        "(",
        ParserEntry {
            parser: Rc::new(|p| p.paren_term()),
            precedence: Precedence::MAX,
            name: "parenthesized expression".to_string(),
            example: Some("(x + y) * z".to_string()),
            help: Some("Group expressions with parentheses".to_string()),
        },
    );

    // Implicit arguments
    term_category.tables.add_leading(
        "{",
        ParserEntry {
            parser: Rc::new(|p| p.implicit_term()),
            precedence: Precedence::MAX,
            name: "implicit argument".to_string(),
            example: Some("{α : Type}".to_string()),
            help: Some("Implicit arguments are inferred by Lean".to_string()),
        },
    );

    // Instance implicit arguments
    term_category.tables.add_leading(
        "[",
        ParserEntry {
            parser: Rc::new(|p| p.inst_implicit_term()),
            precedence: Precedence::MAX,
            name: "instance implicit argument".to_string(),
            example: Some("[Monad m]".to_string()),
            help: Some("Instance arguments resolved by type class inference".to_string()),
        },
    );

    // Syntax quotations
    term_category.tables.add_leading(
        "`",
        ParserEntry {
            parser: Rc::new(|p| {
                if p.input().peek_nth(1) == Some('(') {
                    p.parse_syntax_quotation()
                } else {
                    // Regular identifier with backticks
                    p.atom_term()
                }
            }),
            precedence: Precedence::MAX,
            name: "syntax quotation".to_string(),
            example: Some("`(x + 1)".to_string()),
            help: Some("Quote syntax for use in macros".to_string()),
        },
    );

    // Prefix/unary operators
    term_category.tables.add_leading(
        "-",
        ParserEntry {
            parser: Rc::new(|p| {
                let start = p.position();
                p.advance(); // consume '-'
                p.skip_whitespace();
                let operand = p.with_category("term", |p| {
                    p.parse_category(crate::precedence::Precedence(100))
                })?;
                let range = p.input().range_from(start);
                Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
                    kind: lean_syn_expr::SyntaxKind::UnaryOp,
                    range,
                    children: vec![
                        Syntax::Atom(lean_syn_expr::SyntaxAtom {
                            range: p.input().range_from(start),
                            value: eterned::BaseCoword::new("-"),
                        }),
                        operand,
                    ]
                    .into(),
                })))
            }),
            precedence: crate::precedence::Precedence(100),
            name: "negation".to_string(),
            example: Some("-x".to_string()),
            help: Some("Numeric negation".to_string()),
        },
    );

    term_category.tables.add_leading(
        "!",
        ParserEntry {
            parser: Rc::new(|p| {
                let start = p.position();
                p.advance(); // consume '!'
                p.skip_whitespace();
                let operand = p.with_category("term", |p| {
                    p.parse_category(crate::precedence::Precedence(100))
                })?;
                let range = p.input().range_from(start);
                Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
                    kind: lean_syn_expr::SyntaxKind::UnaryOp,
                    range,
                    children: vec![
                        Syntax::Atom(lean_syn_expr::SyntaxAtom {
                            range: p.input().range_from(start),
                            value: eterned::BaseCoword::new("!"),
                        }),
                        operand,
                    ]
                    .into(),
                })))
            }),
            precedence: crate::precedence::Precedence(100),
            name: "logical not".to_string(),
            example: Some("!p".to_string()),
            help: Some("Logical negation".to_string()),
        },
    );

    term_category.tables.add_leading(
        "¬",
        ParserEntry {
            parser: Rc::new(|p| {
                let start = p.position();
                p.advance(); // consume '¬'
                p.skip_whitespace();
                let operand = p.with_category("term", |p| {
                    p.parse_category(crate::precedence::Precedence(100))
                })?;
                let range = p.input().range_from(start);
                Ok(Syntax::Node(Box::new(lean_syn_expr::SyntaxNode {
                    kind: lean_syn_expr::SyntaxKind::UnaryOp,
                    range,
                    children: vec![
                        Syntax::Atom(lean_syn_expr::SyntaxAtom {
                            range: p.input().range_from(start),
                            value: eterned::BaseCoword::new("¬"),
                        }),
                        operand,
                    ]
                    .into(),
                })))
            }),
            precedence: crate::precedence::Precedence(100),
            name: "logical not".to_string(),
            example: Some("¬p".to_string()),
            help: Some("Logical negation (Unicode)".to_string()),
        },
    );

    // Default parsers for atoms
    term_category.tables.add_default(ParserEntry {
        parser: Rc::new(|p| p.atom_term()),
        precedence: Precedence::MAX,
        name: "atomic term".to_string(),
        example: Some("x, 42, \"hello\"".to_string()),
        help: Some("Basic terms like identifiers, numbers, and strings".to_string()),
    });

    // Add trailing operators
    // Arrow types
    term_category.tables.add_trailing(
        "->",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)), // Handled by parse_trailing
            precedence: crate::precedence::Precedence::ARROW,
            name: "function type".to_string(),
            example: Some("α -> β".to_string()),
            help: Some("Function type from α to β".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "→",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)), // Handled by parse_trailing
            precedence: crate::precedence::Precedence::ARROW,
            name: "function type".to_string(),
            example: Some("α → β".to_string()),
            help: Some("Function type from α to β".to_string()),
        },
    );

    // Logical operators
    term_category.tables.add_trailing(
        "||",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::OR,
            name: "logical or".to_string(),
            example: Some("p || q".to_string()),
            help: Some("Logical disjunction".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "∨",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::OR,
            name: "logical or".to_string(),
            example: Some("p ∨ q".to_string()),
            help: Some("Logical disjunction (Unicode)".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "&&",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::AND,
            name: "logical and".to_string(),
            example: Some("p && q".to_string()),
            help: Some("Logical conjunction".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "∧",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::AND,
            name: "logical and".to_string(),
            example: Some("p ∧ q".to_string()),
            help: Some("Logical conjunction (Unicode)".to_string()),
        },
    );

    // Comparison operators
    term_category.tables.add_trailing(
        "==",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "equality".to_string(),
            example: Some("x == y".to_string()),
            help: Some("Definitional equality".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "=",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "equality".to_string(),
            example: Some("x = y".to_string()),
            help: Some("Propositional equality".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "!=",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "inequality".to_string(),
            example: Some("x != y".to_string()),
            help: Some("Not equal".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "≠",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "inequality".to_string(),
            example: Some("x ≠ y".to_string()),
            help: Some("Not equal (Unicode)".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "<",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "less than".to_string(),
            example: Some("x < y".to_string()),
            help: Some("Less than comparison".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "<=",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "less than or equal".to_string(),
            example: Some("x <= y".to_string()),
            help: Some("Less than or equal comparison".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "≤",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "less than or equal".to_string(),
            example: Some("x ≤ y".to_string()),
            help: Some("Less than or equal (Unicode)".to_string()),
        },
    );

    term_category.tables.add_trailing(
        ">",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "greater than".to_string(),
            example: Some("x > y".to_string()),
            help: Some("Greater than comparison".to_string()),
        },
    );

    term_category.tables.add_trailing(
        ">=",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "greater than or equal".to_string(),
            example: Some("x >= y".to_string()),
            help: Some("Greater than or equal comparison".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "≥",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::CMP,
            name: "greater than or equal".to_string(),
            example: Some("x ≥ y".to_string()),
            help: Some("Greater than or equal (Unicode)".to_string()),
        },
    );

    // Arithmetic operators
    term_category.tables.add_trailing(
        "+",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::ADD,
            name: "addition".to_string(),
            example: Some("x + y".to_string()),
            help: Some("Addition operator".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "-",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::ADD,
            name: "subtraction".to_string(),
            example: Some("x - y".to_string()),
            help: Some("Subtraction operator".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "*",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::MUL,
            name: "multiplication".to_string(),
            example: Some("x * y".to_string()),
            help: Some("Multiplication operator".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "/",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::MUL,
            name: "division".to_string(),
            example: Some("x / y".to_string()),
            help: Some("Division operator".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "^",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::POW,
            name: "exponentiation".to_string(),
            example: Some("x ^ n".to_string()),
            help: Some("Power/exponentiation operator".to_string()),
        },
    );

    // Function composition
    term_category.tables.add_trailing(
        "∘",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence::COMPOSE,
            name: "composition".to_string(),
            example: Some("f ∘ g".to_string()),
            help: Some("Function composition".to_string()),
        },
    );

    // List operations
    term_category.tables.add_trailing(
        "::",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence(67),
            name: "list cons".to_string(),
            example: Some("x :: xs".to_string()),
            help: Some("List construction".to_string()),
        },
    );

    term_category.tables.add_trailing(
        "++",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence(65),
            name: "list append".to_string(),
            example: Some("xs ++ ys".to_string()),
            help: Some("List concatenation".to_string()),
        },
    );

    // Add recovery hints
    term_category.add_recovery_hint(RecoveryHint {
        when_seeing: ";".to_string(),
        suggest: "add parentheses to group expressions".to_string(),
        help: Some("semicolon ';' is used to separate tactics, not terms".to_string()),
        example: Some("(expr1) (expr2) instead of expr1; expr2".to_string()),
    });

    term_category.add_recovery_hint(RecoveryHint {
        when_seeing: "=>".to_string(),
        suggest: "use 'fun x => ...' for lambda expressions".to_string(),
        help: Some("'=>' must be preceded by parameter bindings".to_string()),
        example: Some("fun x => x + 1".to_string()),
    });

    registry.register(term_category);

    // Tactic category
    let mut tactic_category = ParserCategory::new("tactic", LeadingIdentBehavior::Both);

    // Add leading parsers for tactics
    tactic_category.tables.add_leading(
        "exact",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_exact()),
            precedence: Precedence::MAX,
            name: "exact tactic".to_string(),
            example: Some("exact h".to_string()),
            help: Some("Provide exact proof term".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "apply",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_apply()),
            precedence: Precedence::MAX,
            name: "apply tactic".to_string(),
            example: Some("apply theorem_name".to_string()),
            help: Some("Apply a theorem or hypothesis".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "intro",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_intro()),
            precedence: Precedence::MAX,
            name: "intro tactic".to_string(),
            example: Some("intro x y".to_string()),
            help: Some("Introduce hypotheses".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "intros",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_intro()), // Same as intro
            precedence: Precedence::MAX,
            name: "intros tactic".to_string(),
            example: Some("intros x y z".to_string()),
            help: Some("Introduce multiple hypotheses".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "cases",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_cases()),
            precedence: Precedence::MAX,
            name: "cases tactic".to_string(),
            example: Some("cases h with | inl a => ... | inr b => ...".to_string()),
            help: Some("Case analysis on inductive types".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "induction",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_induction()),
            precedence: Precedence::MAX,
            name: "induction tactic".to_string(),
            example: Some("induction n with | zero => ... | succ n' ih => ...".to_string()),
            help: Some("Proof by induction".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "simp",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_simp()),
            precedence: Precedence::MAX,
            name: "simp tactic".to_string(),
            example: Some("simp [theorem1, theorem2]".to_string()),
            help: Some("Simplify using simp lemmas".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "rw",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_rewrite()),
            precedence: Precedence::MAX,
            name: "rewrite tactic".to_string(),
            example: Some("rw [theorem1, ←theorem2]".to_string()),
            help: Some("Rewrite using equalities".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "rewrite",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_rewrite()),
            precedence: Precedence::MAX,
            name: "rewrite tactic".to_string(),
            example: Some("rewrite [theorem1, ←theorem2]".to_string()),
            help: Some("Rewrite using equalities (long form)".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "constructor",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_constructor()),
            precedence: Precedence::MAX,
            name: "constructor tactic".to_string(),
            example: Some("constructor".to_string()),
            help: Some("Apply the first constructor".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "assumption",
        ParserEntry {
            parser: Rc::new(|p| p.parse_tactic_assumption()),
            precedence: Precedence::MAX,
            name: "assumption tactic".to_string(),
            example: Some("assumption".to_string()),
            help: Some("Solve goal using an assumption".to_string()),
        },
    );

    tactic_category.tables.add_leading(
        "calc",
        ParserEntry {
            parser: Rc::new(|p| p.calc_tactic()),
            precedence: Precedence::MAX,
            name: "calc tactic".to_string(),
            example: Some("calc a = b := by rw [h1]\n    _ = c := by rw [h2]".to_string()),
            help: Some("Calculational proof".to_string()),
        },
    );

    // Add tactic combinators as trailing operators
    tactic_category.tables.add_trailing(
        ";",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence(30), // Low precedence
            name: "tactic sequence".to_string(),
            example: Some("tactic1; tactic2".to_string()),
            help: Some("Execute tactics in sequence".to_string()),
        },
    );

    tactic_category.tables.add_trailing(
        "<|>",
        ParserEntry {
            parser: Rc::new(|_p| Ok(Syntax::Missing)),
            precedence: crate::precedence::Precedence(20), // Lower than ;
            name: "tactic alternative".to_string(),
            example: Some("tactic1 <|> tactic2".to_string()),
            help: Some("Try first tactic, if it fails try second".to_string()),
        },
    );

    // Add recovery hints
    tactic_category.add_recovery_hint(RecoveryHint {
        when_seeing: "->".to_string(),
        suggest: "use '=>' in match expressions within tactics".to_string(),
        help: Some("'->' is for function types, not pattern matching".to_string()),
        example: Some("cases h with | inl a => ... | inr b => ...".to_string()),
    });

    tactic_category.add_recovery_hint(RecoveryHint {
        when_seeing: "|".to_string(),
        suggest: "use 'with' before case alternatives".to_string(),
        help: Some("Case alternatives must be preceded by 'with'".to_string()),
        example: Some("cases h with | case1 => ... | case2 => ...".to_string()),
    });

    registry.register(tactic_category);

    // Command category
    let mut command_category = ParserCategory::new("command", LeadingIdentBehavior::Keyword);

    // Add leading parsers for commands
    command_category.tables.add_leading(
        "def",
        ParserEntry {
            parser: Rc::new(|p| p.def_command()),
            precedence: Precedence::MAX,
            name: "definition".to_string(),
            example: Some("def foo (x : Nat) : Nat := x + 1".to_string()),
            help: Some("Define a function or constant".to_string()),
        },
    );

    command_category.tables.add_leading(
        "theorem",
        ParserEntry {
            parser: Rc::new(|p| p.theorem_command()),
            precedence: Precedence::MAX,
            name: "theorem".to_string(),
            example: Some("theorem foo : P := proof".to_string()),
            help: Some("State and prove a theorem".to_string()),
        },
    );

    command_category.tables.add_leading(
        "lemma",
        ParserEntry {
            parser: Rc::new(|p| p.theorem_command()), // Same as theorem
            precedence: Precedence::MAX,
            name: "lemma".to_string(),
            example: Some("lemma foo : P := proof".to_string()),
            help: Some("State and prove a lemma (synonym for theorem)".to_string()),
        },
    );

    command_category.tables.add_leading(
        "axiom",
        ParserEntry {
            parser: Rc::new(|p| p.axiom_command()),
            precedence: Precedence::MAX,
            name: "axiom".to_string(),
            example: Some("axiom em : ∀ p, p ∨ ¬p".to_string()),
            help: Some("Declare an axiom".to_string()),
        },
    );

    command_category.tables.add_leading(
        "constant",
        ParserEntry {
            parser: Rc::new(|p| p.constant_command()),
            precedence: Precedence::MAX,
            name: "constant".to_string(),
            example: Some("constant c : Type".to_string()),
            help: Some("Declare a constant".to_string()),
        },
    );

    command_category.tables.add_leading(
        "variable",
        ParserEntry {
            parser: Rc::new(|p| p.variable_command()),
            precedence: Precedence::MAX,
            name: "variable".to_string(),
            example: Some("variable (α : Type) [Monad m]".to_string()),
            help: Some("Declare variables for the current scope".to_string()),
        },
    );

    command_category.tables.add_leading(
        "universe",
        ParserEntry {
            parser: Rc::new(|p| p.universe_command()),
            precedence: Precedence::MAX,
            name: "universe".to_string(),
            example: Some("universe u v".to_string()),
            help: Some("Declare universe variables".to_string()),
        },
    );

    command_category.tables.add_leading(
        "import",
        ParserEntry {
            parser: Rc::new(|p| p.import_command()),
            precedence: Precedence::MAX,
            name: "import".to_string(),
            example: Some("import Mathlib.Data.List.Basic".to_string()),
            help: Some("Import a module".to_string()),
        },
    );

    command_category.tables.add_leading(
        "open",
        ParserEntry {
            parser: Rc::new(|p| p.open_command()),
            precedence: Precedence::MAX,
            name: "open".to_string(),
            example: Some("open List (map filter)".to_string()),
            help: Some("Open a namespace".to_string()),
        },
    );

    command_category.tables.add_leading(
        "namespace",
        ParserEntry {
            parser: Rc::new(|p| p.namespace_command()),
            precedence: Precedence::MAX,
            name: "namespace".to_string(),
            example: Some("namespace Foo".to_string()),
            help: Some("Enter a namespace".to_string()),
        },
    );

    command_category.tables.add_leading(
        "end",
        ParserEntry {
            parser: Rc::new(|p| p.end_command()),
            precedence: Precedence::MAX,
            name: "end".to_string(),
            example: Some("end Foo".to_string()),
            help: Some("End a namespace or section".to_string()),
        },
    );

    command_category.tables.add_leading(
        "section",
        ParserEntry {
            parser: Rc::new(|p| p.section_command()),
            precedence: Precedence::MAX,
            name: "section".to_string(),
            example: Some("section MySection".to_string()),
            help: Some("Begin a section".to_string()),
        },
    );

    command_category.tables.add_leading(
        "class",
        ParserEntry {
            parser: Rc::new(|p| p.class_command()),
            precedence: Precedence::MAX,
            name: "class".to_string(),
            example: Some("class Monad (m : Type → Type) where ...".to_string()),
            help: Some("Define a type class".to_string()),
        },
    );

    command_category.tables.add_leading(
        "instance",
        ParserEntry {
            parser: Rc::new(|p| p.instance_command()),
            precedence: Precedence::MAX,
            name: "instance".to_string(),
            example: Some("instance : Monad Option where ...".to_string()),
            help: Some("Define a type class instance".to_string()),
        },
    );

    command_category.tables.add_leading(
        "structure",
        ParserEntry {
            parser: Rc::new(|p| p.structure_command()),
            precedence: Precedence::MAX,
            name: "structure".to_string(),
            example: Some("structure Point where x : Float; y : Float".to_string()),
            help: Some("Define a structure".to_string()),
        },
    );

    command_category.tables.add_leading(
        "inductive",
        ParserEntry {
            parser: Rc::new(|p| p.inductive_command()),
            precedence: Precedence::MAX,
            name: "inductive".to_string(),
            example: Some(
                "inductive List (α : Type) | nil | cons : α → List α → List α".to_string(),
            ),
            help: Some("Define an inductive type".to_string()),
        },
    );

    // Hash commands
    command_category.tables.add_leading(
        "#check",
        ParserEntry {
            parser: Rc::new(|p| p.hash_command()),
            precedence: Precedence::MAX,
            name: "check command".to_string(),
            example: Some("#check Nat.add".to_string()),
            help: Some("Check the type of an expression".to_string()),
        },
    );

    command_category.tables.add_leading(
        "#eval",
        ParserEntry {
            parser: Rc::new(|p| p.hash_command()),
            precedence: Precedence::MAX,
            name: "eval command".to_string(),
            example: Some("#eval 2 + 2".to_string()),
            help: Some("Evaluate an expression".to_string()),
        },
    );

    command_category.tables.add_leading(
        "#print",
        ParserEntry {
            parser: Rc::new(|p| p.hash_command()),
            precedence: Precedence::MAX,
            name: "print command".to_string(),
            example: Some("#print Nat".to_string()),
            help: Some("Print information about a definition".to_string()),
        },
    );

    command_category.tables.add_leading(
        "#reduce",
        ParserEntry {
            parser: Rc::new(|p| p.hash_command()),
            precedence: Precedence::MAX,
            name: "reduce command".to_string(),
            example: Some("#reduce 2 + 2".to_string()),
            help: Some("Reduce an expression".to_string()),
        },
    );

    // Macro and notation commands
    command_category.tables.add_leading(
        "macro",
        ParserEntry {
            parser: Rc::new(|p| p.macro_def()),
            precedence: Precedence::MAX,
            name: "macro definition".to_string(),
            example: Some("macro \"test\" : term => `(42)".to_string()),
            help: Some("Define a macro".to_string()),
        },
    );

    command_category.tables.add_leading(
        "macro_rules",
        ParserEntry {
            parser: Rc::new(|p| p.macro_rules()),
            precedence: Precedence::MAX,
            name: "macro rules".to_string(),
            example: Some("macro_rules | x => `($x + 1)".to_string()),
            help: Some("Define macro expansion rules".to_string()),
        },
    );

    command_category.tables.add_leading(
        "syntax",
        ParserEntry {
            parser: Rc::new(|p| p.syntax_def()),
            precedence: Precedence::MAX,
            name: "syntax declaration".to_string(),
            example: Some("syntax \"test\" : term".to_string()),
            help: Some("Declare new syntax".to_string()),
        },
    );

    command_category.tables.add_leading(
        "notation",
        ParserEntry {
            parser: Rc::new(|p| p.notation_def()),
            precedence: Precedence::MAX,
            name: "notation definition".to_string(),
            example: Some("notation \"x ∈ S\" => Membership.mem x S".to_string()),
            help: Some("Define notation".to_string()),
        },
    );

    // Add recovery hints for common mistakes
    command_category.add_recovery_hint(RecoveryHint {
        when_seeing: ":=".to_string(),
        suggest: "add 'def' or 'theorem' before the name".to_string(),
        help: Some("Definitions require a command keyword".to_string()),
        example: Some("def myFunction := ...".to_string()),
    });

    command_category.add_recovery_hint(RecoveryHint {
        when_seeing: "let".to_string(),
        suggest: "use 'def' for top-level definitions".to_string(),
        help: Some("'let' is for local bindings, use 'def' at top level".to_string()),
        example: Some("def myValue := 42".to_string()),
    });

    registry.register(command_category);

    registry
}
