//! Scoped notation and attributes for Lean 4
//!
//! This module implements scoped notation declarations and attribute management.
//! Scoped notations allow defining custom syntax that is only active within
//! specific namespaces or sections.

use lean_syn_expr::{Syntax, SyntaxAtom, SyntaxKind, SyntaxNode};
use smallvec::{smallvec, SmallVec};

use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse scoped notation declaration
    /// Examples:
    /// - `scoped notation "⟨" x "," y "⟩" => Prod.mk x y`
    /// - `scoped[Ring] notation "x ^ n" => pow x n`
    pub fn scoped_notation(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("scoped")?;
        self.skip_whitespace();
        
        let mut children = SmallVec::new();
        
        // Parse optional scope specification [ScopeName]
        let scope = if self.peek() == Some('[') {
            self.advance(); // consume '['
            self.skip_whitespace();
            
            let scope_name = self.identifier()?;
            
            self.skip_whitespace();
            self.expect_char(']')?;
            self.skip_whitespace();
            
            Some(scope_name)
        } else {
            None
        };
        
        if let Some(s) = scope {
            children.push(s);
        }
        
        // Now parse the notation itself
        self.keyword("notation")?;
        self.skip_whitespace();
        
        // Parse optional fixity and precedence
        if self.peek_keyword("infix") || self.peek_keyword("prefix") || self.peek_keyword("postfix") {
            children.push(self.scoped_notation_fixity()?);
            self.skip_whitespace();
        }
        
        if self.peek() == Some(':') {
            self.advance();
            children.push(self.precedence_spec()?);
            self.skip_whitespace();
        }
        
        // Parse notation pattern
        if self.peek() == Some('"') {
            // Simple string notation
            children.push(self.string_literal()?);
            self.skip_whitespace();
            
            // Parse more string parts and parameters for mixfix notation
            while !self.peek_keyword("=>") && self.peek().is_some() {
                if self.peek() == Some('"') {
                    children.push(self.string_literal()?);
                } else if self.peek().is_some_and(|c| c.is_alphabetic()) {
                    children.push(self.identifier()?);
                } else {
                    break;
                }
                self.skip_whitespace();
            }
        } else {
            // Could be a mixfix notation with parameters
            while !self.peek_keyword("=>") && self.peek().is_some() {
                if self.peek() == Some('"') {
                    children.push(self.string_literal()?);
                } else if self.peek().is_some_and(|c| c.is_alphabetic()) {
                    children.push(self.identifier()?);
                } else {
                    break;
                }
                self.skip_whitespace();
            }
        }
        
        self.skip_whitespace();
        
        // Now parse =>
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
        
        // Parse expansion
        children.push(self.term()?);
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::ScopedNotation,
            range,
            children,
        })))
    }
    
    /// Parse attribute declaration
    /// Examples:
    /// - `@[simp] lemma foo : ...`
    /// - `@[inline, reducible] def bar : ...`
    /// - `@[simp ←] lemma reverse_simp : ...`
    pub fn parse_scoped_attribute_list(&mut self) -> ParserResult<Vec<Syntax>> {
        let mut attributes = Vec::new();
        
        while self.peek() == Some('@') && self.input().peek_nth(1) == Some('[') {
            let start = self.position();
            
            self.advance(); // consume '@'
            self.advance(); // consume '['
            self.skip_whitespace();
            
            let mut attrs = Vec::new();
            
            while self.peek() != Some(']') {
                let attr = self.parse_single_attr()?;
                attrs.push(attr);
                
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
            self.skip_whitespace();
            
            let range = self.input().range_from(start);
            attributes.push(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::Attribute,
                range,
                children: attrs.into(),
            })));
        }
        
        Ok(attributes)
    }
    
    /// Parse a single attribute with optional arguments
    fn parse_single_attr(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut children = SmallVec::new();
        
        // Parse attribute name
        let name = self.identifier()?;
        children.push(name);
        
        self.skip_whitespace();
        
        // Parse optional direction (← or →)
        if self.peek() == Some('←') || (self.peek() == Some('<') && self.input().peek_nth(1) == Some('-')) {
            if self.peek() == Some('←') {
                self.advance();
            } else {
                self.advance(); // <
                self.advance(); // -
            }
            children.push(Syntax::Atom(SyntaxAtom {
                range: self.input().range_from(start),
                value: eterned::BaseCoword::new("←"),
            }));
            self.skip_whitespace();
        } else if self.peek() == Some('→') || (self.peek() == Some('-') && self.input().peek_nth(1) == Some('>')) {
            if self.peek() == Some('→') {
                self.advance();
            } else {
                self.advance(); // -
                self.advance(); // >
            }
            children.push(Syntax::Atom(SyntaxAtom {
                range: self.input().range_from(start),
                value: eterned::BaseCoword::new("→"),
            }));
            self.skip_whitespace();
        }
        
        // Parse optional arguments
        if self.peek() == Some('(') || self.peek().is_some_and(|c| c.is_alphabetic() || c.is_ascii_digit()) {
            // Could have arguments like simp (config := {...}) or inline (always)
            if self.peek() == Some('(') {
                // For now, just consume the parenthesized content
                self.advance(); // (
                let arg_start = self.position();
                let mut depth = 1;
                while depth > 0 && self.peek().is_some() {
                    match self.peek() {
                        Some('(') => depth += 1,
                        Some(')') => depth -= 1,
                        _ => {}
                    }
                    if depth > 0 {
                        self.advance();
                    }
                }
                self.expect_char(')')?;
                children.push(Syntax::Atom(SyntaxAtom {
                    range: self.input().range_from(arg_start),
                    value: eterned::BaseCoword::new("config"),
                }));
            } else {
                // Simple argument
                children.push(self.identifier()?);
            }
        }
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::AttributeInstance,
            range,
            children,
        })))
    }
    
    /// Parse local notation (active only within current section/namespace)
    /// Example: `local notation "⟨" x "⟩" => Singleton.mk x`
    pub fn local_notation(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("local")?;
        self.skip_whitespace();
        
        let mut children = smallvec![
            Syntax::Atom(SyntaxAtom {
                range: self.input().range_from(start),
                value: eterned::BaseCoword::new("local"),
            })
        ];
        
        // Parse the notation command
        let notation = self.notation_command()?;
        children.push(notation);
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::LocalNotation,
            range,
            children,
        })))
    }
    
    /// Parse macro_rules for custom syntax extensions
    /// Example:
    /// ```lean
    /// macro_rules
    ///   | `(tactic| trivial) => `(tactic| (first | rfl | simp | omega))
    /// ```
    pub fn scoped_macro_rules(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("macro_rules")?;
        self.skip_whitespace_and_comments();
        
        let mut rules = Vec::new();
        
        // Parse macro rules (each starts with |)
        while self.peek() == Some('|') {
            self.advance(); // consume '|'
            self.skip_whitespace();
            
            // Parse pattern: `(category| pattern)
            let pattern = self.parse_scoped_macro_pattern()?;
            
            self.skip_whitespace();
            self.expect_char('=')?;
            self.expect_char('>')?;
            self.skip_whitespace();
            
            // Parse expansion
            let expansion = self.parse_macro_expansion()?;
            
            rules.push(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::MacroRule,
                range: self.input().range_from(start),
                children: smallvec![pattern, expansion],
            })));
            
            self.skip_whitespace_and_comments();
        }
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::MacroRules,
            range,
            children: rules.into(),
        })))
    }
    
    /// Parse macro pattern: `(category| pattern)
    fn parse_scoped_macro_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        // Expect backtick
        self.expect_char('`')?;
        self.expect_char('(')?;
        self.skip_whitespace();
        
        // Parse category
        let category = self.identifier()?;
        self.skip_whitespace();
        
        self.expect_char('|')?;
        self.skip_whitespace();
        
        // Parse pattern - for now, just consume until closing paren
        let pattern_start = self.position();
        let mut depth = 1;
        let mut pattern_text = String::new();
        
        while depth > 0 && self.peek().is_some() {
            let ch = self.peek().unwrap();
            if ch == '(' {
                depth += 1;
            } else if ch == ')' {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            pattern_text.push(ch);
            self.advance();
        }
        
        self.expect_char(')')?;
        
        let pattern = Syntax::Atom(SyntaxAtom {
            range: self.input().range_from(pattern_start),
            value: eterned::BaseCoword::new(&pattern_text),
        });
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::MacroPattern,
            range,
            children: smallvec![category, pattern],
        })))
    }
    
    /// Parse macro expansion
    fn parse_macro_expansion(&mut self) -> ParserResult<Syntax> {
        // Similar to pattern parsing
        let start = self.position();
        
        self.expect_char('`')?;
        self.expect_char('(')?;
        self.skip_whitespace();
        
        // Parse category
        let category = self.identifier()?;
        self.skip_whitespace();
        
        self.expect_char('|')?;
        self.skip_whitespace();
        
        // Parse expansion - for now, just consume until closing paren
        let expansion_start = self.position();
        let mut depth = 1;
        let mut expansion_text = String::new();
        
        while depth > 0 && self.peek().is_some() {
            let ch = self.peek().unwrap();
            if ch == '(' {
                depth += 1;
            } else if ch == ')' {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            expansion_text.push(ch);
            self.advance();
        }
        
        self.expect_char(')')?;
        
        let expansion = Syntax::Atom(SyntaxAtom {
            range: self.input().range_from(expansion_start),
            value: eterned::BaseCoword::new(&expansion_text),
        });
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::MacroExpansion,
            range,
            children: smallvec![category, expansion],
        })))
    }
    
    /// Parse syntax declaration for custom categories
    /// Example: `syntax term:max "begin" tactic,* "end" : term`
    pub fn syntax_declaration(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("syntax")?;
        self.skip_whitespace();
        
        let mut children = Vec::new();
        
        // Parse optional precedence binding
        if self.peek().is_some_and(|c| c.is_alphabetic()) && !self.peek_keyword("\"") {
            let binding = self.identifier()?;
            children.push(binding);
            
            if self.peek() == Some(':') {
                self.advance();
                let prec = self.precedence_spec()?;
                children.push(prec);
            }
            self.skip_whitespace();
        }
        
        // Parse syntax pattern
        children.extend(self.parse_scoped_syntax_pattern()?);
        
        self.skip_whitespace();
        self.expect_char(':')?;
        self.skip_whitespace();
        
        // Parse category
        let category = self.identifier()?;
        children.push(category);
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::SyntaxDecl,
            range,
            children: children.into(),
        })))
    }
    
    /// Parse syntax pattern for syntax declarations
    fn parse_scoped_syntax_pattern(&mut self) -> ParserResult<Vec<Syntax>> {
        let mut elements = Vec::new();
        
        while self.peek() != Some(':') && self.peek().is_some() {
            if self.peek() == Some('"') {
                // String literal
                elements.push(self.string_literal()?);
            } else if self.peek().is_some_and(|c| c.is_alphabetic()) {
                // Could be a nonterminal or keyword
                let ident = self.identifier()?;
                self.skip_whitespace();
                
                // Check for repetition operators
                if self.peek() == Some('*') {
                    self.advance();
                    elements.push(Syntax::Node(Box::new(SyntaxNode {
                        kind: SyntaxKind::Repeat,
                        range: self.input().range_from(self.position()),
                        children: smallvec![ident],
                    })));
                } else if self.peek() == Some('+') {
                    self.advance();
                    elements.push(Syntax::Node(Box::new(SyntaxNode {
                        kind: SyntaxKind::Repeat,
                        range: self.input().range_from(self.position()),
                        children: smallvec![ident],
                    })));
                } else if self.peek() == Some('?') {
                    self.advance();
                    elements.push(Syntax::Node(Box::new(SyntaxNode {
                        kind: SyntaxKind::Optional,
                        range: self.input().range_from(self.position()),
                        children: smallvec![ident],
                    })));
                } else {
                    elements.push(ident);
                }
            } else if self.peek() == Some(',') {
                // Separator
                self.advance();
                elements.push(Syntax::Atom(SyntaxAtom {
                    range: self.input().range_from(self.position()),
                    value: eterned::BaseCoword::new(","),
                }));
            } else {
                break;
            }
            
            self.skip_whitespace();
        }
        
        Ok(elements)
    }
    
    /// Parse notation fixity helper
    fn scoped_notation_fixity(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        let fixity = if self.peek_keyword("infix") {
            self.keyword("infix")?;
            "infix"
        } else if self.peek_keyword("prefix") {
            self.keyword("prefix")?;
            "prefix"
        } else if self.peek_keyword("postfix") {
            self.keyword("postfix")?;
            "postfix"
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("fixity specifier".to_string()),
                self.position(),
            ));
        };
        
        let range = self.input().range_from(start);
        Ok(Syntax::Atom(SyntaxAtom {
            range,
            value: eterned::BaseCoword::new(fixity),
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    fn parse_scoped(input: &str) -> ParserResult<Syntax> {
        let mut parser = Parser::new(input);
        parser.scoped_notation()
    }
    
    fn parse_attrs(input: &str) -> ParserResult<Vec<Syntax>> {
        let mut parser = Parser::new(input);
        parser.parse_scoped_attribute_list()
    }
    
    #[test]
    fn test_scoped_notation() {
        let result = parse_scoped(r#"scoped notation "⟨" x "," y "⟩" => Prod.mk x y"#).unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::ScopedNotation));
    }
    
    #[test]
    fn test_scoped_with_namespace() {
        let result = parse_scoped(r#"scoped[Ring] notation "x ^ n" => pow x n"#).unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::ScopedNotation));
    }
    
    #[test]
    fn test_attributes() {
        let result = parse_attrs("@[simp]").unwrap();
        assert_eq!(result.len(), 1);
        
        let result = parse_attrs("@[inline, reducible]").unwrap();
        assert_eq!(result.len(), 1);
        
        let result = parse_attrs("@[simp ←]").unwrap();
        assert_eq!(result.len(), 1);
    }
}