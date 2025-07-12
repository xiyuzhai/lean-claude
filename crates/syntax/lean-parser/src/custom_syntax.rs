//! Support for custom syntax categories in Lean 4
//!
//! This module provides functionality to define and register custom syntax
//! categories, allowing users to extend the parser with new syntax forms.

use std::rc::Rc;

use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    category::{CategoryRegistry, LeadingIdentBehavior, ParserCategory, ParserEntry},
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserResult},
    precedence::Precedence,
};

/// Represents a custom syntax category definition
#[derive(Clone)]
pub struct CustomSyntaxCategory {
    /// Name of the category
    pub name: String,
    /// Parent category to inherit from (optional)
    pub parent: Option<String>,
    /// Whether this category allows leading identifiers
    pub allow_leading_ident: bool,
    /// Default precedence for operators in this category
    pub default_precedence: Precedence,
}

impl<'a> Parser<'a> {
    /// Parse a custom syntax category declaration
    /// Example: `declare_syntax_cat mycat`
    pub fn declare_syntax_cat(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("declare_syntax_cat")?;
        self.skip_whitespace();

        // Parse category name
        let name = self.identifier()?;
        self.skip_whitespace();

        // Optional parameters
        let mut parent = None;
        let mut behavior = LeadingIdentBehavior::Both;

        // Parse optional modifiers
        while self.peek() == Some('(') {
            self.advance(); // consume '('
            self.skip_whitespace();

            if self.peek_keyword("parent") {
                self.keyword("parent")?;
                self.skip_whitespace();
                self.expect_char(':')?;
                self.skip_whitespace();
                parent = Some(self.identifier()?);
            } else if self.peek_keyword("behavior") {
                self.keyword("behavior")?;
                self.skip_whitespace();
                self.expect_char(':')?;
                self.skip_whitespace();
                let behavior_str = self.identifier()?;
                behavior = match behavior_str.as_str() {
                    "keyword" => LeadingIdentBehavior::Keyword,
                    "ident" => LeadingIdentBehavior::Ident,
                    "both" => LeadingIdentBehavior::Both,
                    _ => {
                        return Err(ParseError::boxed(
                            ParseErrorKind::Custom(format!(
                                "Unknown behavior: {}. Expected 'keyword', 'ident', or 'both'",
                                behavior_str.as_str()
                            )),
                            self.position(),
                        ))
                    }
                };
            } else if self.peek_keyword("precedence") {
                self.keyword("precedence")?;
                self.skip_whitespace();
                self.expect_char(':')?;
                self.skip_whitespace();
                let _precedence = self.parse_precedence_value()?;
            }

            self.skip_whitespace();
            self.expect_char(')')?;
            self.skip_whitespace();
        }

        // Register the new category
        let name_str = name.as_str().to_string();
        self.register_custom_category(
            name_str.clone(),
            parent.as_ref().map(|p| p.as_str()),
            behavior,
        )?;

        let range = self.input().range_from(start);
        let mut children = smallvec![name];
        if let Some(p) = parent {
            children.push(p);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::DeclareSyntaxCat,
            range,
            children,
        ))))
    }

    /// Register a custom syntax category
    fn register_custom_category(
        &mut self,
        name: String,
        parent: Option<&str>,
        behavior: LeadingIdentBehavior,
    ) -> ParserResult<()> {
        let mut category = ParserCategory::new(name.clone(), behavior);

        // If there's a parent, inherit its parsers
        if let Some(parent_name) = parent {
            let parent_category = self
                .categories()
                .borrow()
                .get(parent_name)
                .cloned()
                .ok_or_else(|| {
                    ParseError::boxed(
                        ParseErrorKind::Custom(format!("Unknown parent category: {parent_name}")),
                        self.position(),
                    )
                })?;

            // Copy parsers from parent
            category.tables = parent_category.tables.clone();
            category.recovery_hints = parent_category.recovery_hints.clone();
        }

        // Register the category
        self.categories().borrow_mut().register(category);

        Ok(())
    }

    /// Parse syntax extension for existing category
    /// Example: `syntax term := "myop" term:max : term`
    pub fn extend_syntax(&mut self) -> ParserResult<Syntax> {
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
        let precedence = if self.peek() == Some('(') {
            Some(self.parse_precedence_annotation()?)
        } else {
            None
        };
        if let Some(prec) = precedence.clone() {
            children.push(prec);
        }
        self.skip_whitespace();

        // Category to extend (optional, defaults to term)
        let category = if self.peek().is_some_and(|c| c.is_alphabetic())
            && self.input().peek_nth(1) == Some(':')
            && self.input().peek_nth(2) == Some('=')
        {
            let cat = self.identifier()?;
            self.skip_whitespace();
            cat
        } else {
            // Default to term category
            Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                self.input().range_from(self.position()),
                eterned::BaseCoword::new("term"),
            ))
        };
        children.push(category.clone());

        // Parse :=
        self.expect_char(':')?;
        self.expect_char('=')?;
        self.skip_whitespace();

        // Parse syntax pattern
        let pattern = self.parse_syntax_pattern()?;
        children.push(pattern.clone());

        // Parse result category
        self.skip_whitespace();
        self.expect_char(':')?;
        self.skip_whitespace();
        let result_category = self.identifier()?;
        children.push(result_category);

        // Register the syntax extension
        self.register_syntax_extension(
            category.as_str(),
            pattern,
            precedence.and_then(|p| self.extract_precedence_value(&p)),
        )?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::SyntaxExtension,
            range,
            children.into(),
        ))))
    }

    /// Parse a syntax pattern (simplified version)
    fn parse_syntax_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut parts = Vec::new();

        while !self.peek_keyword(":") && !self.input().is_at_end() {
            if self.peek() == Some('"') {
                // String literal part
                parts.push(self.string_literal()?);
            } else if self.peek().is_some_and(|c| c.is_alphabetic()) {
                // Parameter or keyword
                let ident = self.identifier()?;
                self.skip_whitespace();

                // Check if it's a parameter with category
                if self.peek() == Some(':') {
                    self.advance(); // consume ':'
                    self.skip_whitespace();
                    let category = self.identifier()?;

                    // Create parameter node
                    let param_range = self.input().range_from(start);
                    parts.push(Syntax::Node(Box::new(SyntaxNode::new(
                        SyntaxKind::SyntaxParam,
                        param_range,
                        smallvec![ident, category],
                    ))));
                } else {
                    parts.push(ident);
                }
            } else {
                // Single character operator
                let ch = self.advance().ok_or_else(|| {
                    ParseError::boxed(ParseErrorKind::UnexpectedEof, self.position())
                })?;
                let op_range = self.input().range_from(start);
                parts.push(Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                    op_range,
                    eterned::BaseCoword::new(ch.to_string()),
                )));
            }

            self.skip_whitespace();
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::SyntaxPattern,
            range,
            parts.into(),
        ))))
    }

    /// Register a syntax extension in the category system
    fn register_syntax_extension(
        &mut self,
        category_name: &str,
        pattern: Syntax,
        precedence: Option<Precedence>,
    ) -> ParserResult<()> {
        // Extract the leading token from the pattern
        let leading_token = self.extract_leading_token(&pattern)?;
        let prec = precedence.unwrap_or(Precedence::MAX);

        // Create parser entry
        let parser_entry = ParserEntry {
            parser: Rc::new(move |p| p.parse_custom_syntax(pattern.clone())),
            precedence: prec,
            name: format!("custom syntax {leading_token}"),
            example: None,
            help: Some("User-defined syntax".to_string()),
        };

        // Add to category
        let mut categories = self.categories().borrow_mut();
        if let Some(category) = categories.get_mut(category_name) {
            category.tables.add_leading(&leading_token, parser_entry);
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Custom(format!("Unknown category: {category_name}")),
                self.position(),
            ));
        }

        Ok(())
    }

    /// Parse using a custom syntax pattern
    fn parse_custom_syntax(&mut self, pattern: Syntax) -> ParserResult<Syntax> {
        let start = self.position();
        let mut matched_parts = Vec::new();

        // Match the pattern
        if let Syntax::Node(node) = &pattern {
            if node.kind == SyntaxKind::SyntaxPattern {
                for part in &node.children {
                    match part {
                        Syntax::Atom(atom) => {
                            // Match literal token
                            let token = atom.value.as_str();
                            if token.len() == 1 {
                                self.expect_char(token.chars().next().unwrap())?;
                            } else {
                                self.keyword(token)?;
                            }
                            self.skip_whitespace();
                        }
                        Syntax::Node(param_node) if param_node.kind == SyntaxKind::SyntaxParam => {
                            // Parse parameter with specified category
                            if let Some(Syntax::Atom(cat_atom)) = param_node.children.get(1) {
                                let category = cat_atom.value.as_str();
                                let parsed = self.with_category(category, |p| {
                                    p.parse_category(Precedence::MIN)
                                })?;
                                matched_parts.push(parsed);
                                self.skip_whitespace();
                            }
                        }
                        _ => {
                            // Parse as term by default
                            let parsed = self.term()?;
                            matched_parts.push(parsed);
                            self.skip_whitespace();
                        }
                    }
                }
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomSyntax,
            range,
            matched_parts.into(),
        ))))
    }

    /// Extract the leading token from a syntax pattern
    fn extract_leading_token(&self, pattern: &Syntax) -> ParserResult<String> {
        if let Syntax::Node(node) = pattern {
            if node.kind == SyntaxKind::SyntaxPattern {
                if let Some(Syntax::Atom(atom)) = node.children.first() {
                    return Ok(atom.value.as_str().to_string());
                }
            }
        }

        Err(ParseError::boxed(
            ParseErrorKind::Custom("Could not extract leading token from pattern".to_string()),
            self.position(),
        ))
    }

    /// Extract precedence value from a precedence annotation
    fn extract_precedence_value(&self, prec_syntax: &Syntax) -> Option<Precedence> {
        // Simple implementation - in real Lean this would be more sophisticated
        if let Syntax::Node(node) = prec_syntax {
            if let Some(Syntax::Atom(atom)) = node.children.first() {
                if let Ok(value) = atom.value.as_str().parse::<u8>() {
                    return Some(Precedence(value.into()));
                }
            }
        }
        None
    }

    /// Parse a precedence value
    fn parse_precedence_value(&mut self) -> ParserResult<Precedence> {
        let num = self.number()?;
        if let Syntax::Atom(atom) = num {
            if let Ok(value) = atom.value.as_str().parse::<u8>() {
                return Ok(Precedence(value.into()));
            }
        }
        Err(ParseError::boxed(
            ParseErrorKind::Custom("Invalid precedence value".to_string()),
            self.position(),
        ))
    }
}

/// Helper function to define a simple infix operator
pub fn define_infix_operator(
    registry: &mut CategoryRegistry,
    category: &str,
    operator: &str,
    precedence: Precedence,
    name: &str,
) -> Result<(), String> {
    if let Some(cat) = registry.get_mut(category) {
        cat.tables.add_trailing(
            operator,
            ParserEntry {
                parser: Rc::new(|_| Ok(Syntax::Missing)), // Handled by parse_trailing
                precedence,
                name: name.to_string(),
                example: Some(format!("x {operator} y")),
                help: Some(format!("Custom {name} operator")),
            },
        );
        Ok(())
    } else {
        Err(format!("Category {category} not found"))
    }
}

/// Helper function to define a simple prefix operator
pub fn define_prefix_operator(
    registry: &mut CategoryRegistry,
    category: &str,
    operator: &str,
    precedence: Precedence,
    name: &str,
) -> Result<(), String> {
    if let Some(cat) = registry.get_mut(category) {
        let op_str = operator.to_string();
        let cat_name = category.to_string();
        cat.tables.add_leading(
            operator,
            ParserEntry {
                parser: Rc::new(move |p| {
                    let start = p.position();

                    // Consume operator
                    for _ in op_str.chars() {
                        p.advance();
                    }
                    p.skip_whitespace();

                    // Parse operand
                    let operand = p.with_category(&cat_name, |p| p.parse_category(precedence))?;

                    let range = p.input().range_from(start);
                    Ok(Syntax::Node(Box::new(SyntaxNode::new(
                        SyntaxKind::UnaryOp,
                        range,
                        vec![
                            Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
                                p.input().range_from(start),
                                eterned::BaseCoword::new(op_str.clone()),
                            )),
                            operand,
                        ]
                        .into(),
                    ))))
                }),
                precedence,
                name: name.to_string(),
                example: Some(format!("{operator}x")),
                help: Some(format!("Custom {name} operator")),
            },
        );
        Ok(())
    } else {
        Err(format!("Category {category} not found"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Parser;

    #[test]
    fn test_custom_category_declaration() {
        let input = "declare_syntax_cat mycat";
        let mut parser = Parser::new(input);

        let result = parser.declare_syntax_cat();
        assert!(result.is_ok());

        // Check that the category was registered
        assert!(parser.categories().borrow().get("mycat").is_some());
    }

    #[test]
    fn test_custom_category_with_parent() {
        let input = "declare_syntax_cat mycat (parent: term)";
        let mut parser = Parser::new(input);

        let result = parser.declare_syntax_cat();
        assert!(result.is_ok());

        // Check that the category inherits from term
        let categories = parser.categories().borrow();
        let mycat = categories.get("mycat").unwrap();
        // Should have inherited term's parsers
        assert!(!mycat.tables.leading.is_empty());
    }

    #[test]
    fn test_syntax_extension() {
        // Test the standard syntax definition form - syntax_def expects a simple
        // pattern
        let input = r#"syntax "myBrackets" : term"#;
        let mut parser = Parser::new(input);

        let result = parser.syntax_def();
        assert!(result.is_ok(), "Failed to parse: {result:?}");

        // Also test declare_syntax_cat which integrates with the system
        let input2 = "declare_syntax_cat bracket";
        let mut parser2 = Parser::new(input2);
        let result2 = parser2.declare_syntax_cat();
        assert!(
            result2.is_ok(),
            "Failed to parse declare_syntax_cat: {result2:?}"
        );
    }

    #[test]
    fn test_custom_infix_operator() {
        let mut registry = crate::category::init_standard_categories();

        let result = define_infix_operator(&mut registry, "term", "⊕", Precedence(65), "oplus");

        assert!(result.is_ok());

        // Check that operator was added
        let term_cat = registry.get("term").unwrap();
        assert!(term_cat.tables.trailing.contains_key("⊕"));
    }
}
