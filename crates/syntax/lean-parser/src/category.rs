//! Parser category system inspired by Lean 4's extensible parsing
//! with Rust-style error handling and recovery

use std::collections::HashMap;

use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserFn, ParserResult},
    precedence::Precedence,
};
use lean_syn_expr::Syntax;

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
#[derive(Clone)]
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
        Self {
            leading: HashMap::new(),
            trailing: HashMap::new(),
            default_parsers: Vec::new(),
        }
    }

    /// Add a leading parser (triggered by specific token)
    pub fn add_leading(&mut self, trigger: impl Into<String>, entry: ParserEntry) {
        self.leading
            .entry(trigger.into())
            .or_insert_with(Vec::new)
            .push(entry);
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
        Err(self.expected_error(parser))
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
                let two_char = format!("{}{}", ch1, ch2);
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
                let two_char = format!("{}{}", ch1, ch2);
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
            return Err(ParseError::new(
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
        let right_range = right.range().cloned().unwrap_or(lean_syn_expr::SourceRange {
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
        mut error: ParseError,
        _start_pos: lean_syn_expr::SourcePos,
    ) -> ParseError {
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
        for (token, _) in &self.tables.leading {
            expected.push(format!("'{}'", token));
        }
        if !expected.is_empty() {
            error.add_expected_list(expected);
        }
        
        error
    }

    fn try_recovery<'a>(
        &self,
        _parser: &mut Parser<'a>,
        _error: &ParseError,
    ) -> Option<Syntax> {
        // Implement various recovery strategies
        // For now, return None
        None
    }

    fn expected_error<'a>(&self, parser: &Parser<'a>) -> ParseError {
        let mut expected = Vec::new();
        
        // Collect what we could parse here
        for (_token, entries) in &self.tables.leading {
            if let Some(entry) = entries.first() {
                expected.push(entry.name.clone());
            }
        }
        
        ParseError::new(
            ParseErrorKind::ExpectedOneOf(expected),
            parser.position(),
        )
    }
}

/// Category registry for managing all parser categories
pub struct CategoryRegistry {
    categories: HashMap<String, ParserCategory>,
}

impl CategoryRegistry {
    pub fn new() -> Self {
        Self {
            categories: HashMap::new(),
        }
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
    term_category.tables.add_leading("λ", ParserEntry {
        parser: Rc::new(|p| p.lambda_term()),
        precedence: Precedence::MAX,
        name: "lambda expression".to_string(),
        example: Some("λ x => x + 1".to_string()),
        help: Some("Lambda expressions define anonymous functions".to_string()),
    });
    
    term_category.tables.add_leading("\\", ParserEntry {
        parser: Rc::new(|p| p.lambda_term()),
        precedence: Precedence::MAX,
        name: "lambda expression".to_string(),
        example: Some("\\x => x + 1".to_string()),
        help: Some("Backslash is an ASCII alternative to λ".to_string()),
    });
    
    term_category.tables.add_leading("fun", ParserEntry {
        parser: Rc::new(|p| p.lambda_term()),
        precedence: Precedence::MAX,
        name: "function".to_string(),
        example: Some("fun x => x + 1".to_string()),
        help: Some("'fun' keyword defines anonymous functions".to_string()),
    });
    
    // Forall quantifier
    term_category.tables.add_leading("∀", ParserEntry {
        parser: Rc::new(|p| p.forall_term()),
        precedence: Precedence::MAX,
        name: "universal quantifier".to_string(),
        example: Some("∀ x, P x".to_string()),
        help: Some("Universal quantification over a type".to_string()),
    });
    
    term_category.tables.add_leading("forall", ParserEntry {
        parser: Rc::new(|p| p.forall_term()),
        precedence: Precedence::MAX,
        name: "universal quantifier".to_string(),
        example: Some("forall x, P x".to_string()),
        help: Some("ASCII alternative to ∀".to_string()),
    });
    
    // Let expressions
    term_category.tables.add_leading("let", ParserEntry {
        parser: Rc::new(|p| p.let_term()),
        precedence: Precedence::MAX,
        name: "let expression".to_string(),
        example: Some("let x := 5 in x + 1".to_string()),
        help: Some("Local variable binding".to_string()),
    });
    
    // Have expressions
    term_category.tables.add_leading("have", ParserEntry {
        parser: Rc::new(|p| p.have_term()),
        precedence: Precedence::MAX,
        name: "have expression".to_string(),
        example: Some("have h : P := proof".to_string()),
        help: Some("Introduce a local proof".to_string()),
    });
    
    // Show expressions
    term_category.tables.add_leading("show", ParserEntry {
        parser: Rc::new(|p| p.show_term()),
        precedence: Precedence::MAX,
        name: "show expression".to_string(),
        example: Some("show P from proof".to_string()),
        help: Some("Explicitly state what is being proven".to_string()),
    });
    
    // Match expressions
    term_category.tables.add_leading("match", ParserEntry {
        parser: Rc::new(|p| p.match_expr()),
        precedence: Precedence::MAX,
        name: "match expression".to_string(),
        example: Some("match x with | some y => y | none => 0".to_string()),
        help: Some("Pattern matching on values".to_string()),
    });
    
    // By tactic
    term_category.tables.add_leading("by", ParserEntry {
        parser: Rc::new(|p| p.by_tactic()),
        precedence: Precedence::MAX,
        name: "tactic proof".to_string(),
        example: Some("by exact h".to_string()),
        help: Some("Switch to tactic mode for proving".to_string()),
    });
    
    // Parentheses
    term_category.tables.add_leading("(", ParserEntry {
        parser: Rc::new(|p| p.paren_term()),
        precedence: Precedence::MAX,
        name: "parenthesized expression".to_string(),
        example: Some("(x + y) * z".to_string()),
        help: Some("Group expressions with parentheses".to_string()),
    });
    
    // Implicit arguments
    term_category.tables.add_leading("{", ParserEntry {
        parser: Rc::new(|p| p.implicit_term()),
        precedence: Precedence::MAX,
        name: "implicit argument".to_string(),
        example: Some("{α : Type}".to_string()),
        help: Some("Implicit arguments are inferred by Lean".to_string()),
    });
    
    // Instance implicit arguments
    term_category.tables.add_leading("[", ParserEntry {
        parser: Rc::new(|p| p.inst_implicit_term()),
        precedence: Precedence::MAX,
        name: "instance implicit argument".to_string(),
        example: Some("[Monad m]".to_string()),
        help: Some("Instance arguments resolved by type class inference".to_string()),
    });
    
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
    term_category.tables.add_trailing("->", ParserEntry {
        parser: Rc::new(|_p| todo!("arrow type parser")),
        precedence: Precedence(25),
        name: "function type".to_string(),
        example: Some("α -> β".to_string()),
        help: Some("Function type from α to β".to_string()),
    });
    
    term_category.tables.add_trailing("→", ParserEntry {
        parser: Rc::new(|_p| todo!("arrow type parser")),
        precedence: Precedence(25),
        name: "function type".to_string(),
        example: Some("α → β".to_string()),
        help: Some("Function type from α to β".to_string()),
    });
    
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
    
    tactic_category.add_recovery_hint(RecoveryHint {
        when_seeing: "->".to_string(),
        suggest: "use '=>' in match expressions within tactics".to_string(),
        help: Some("'->' is for function types, not pattern matching".to_string()),
        example: Some("cases h with | inl a => ... | inr b => ...".to_string()),
    });
    
    registry.register(tactic_category);
    
    // Command category
    let command_category = ParserCategory::new("command", LeadingIdentBehavior::Keyword);
    registry.register(command_category);
    
    registry
}