//! Advanced tactic combinators and structured tactics for Lean 4
//!
//! This module implements the tactic combinators that allow
//! sophisticated proof automation in Lean 4.

use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse `repeat` tactic combinator
    pub fn repeat_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("repeat")?;
        self.skip_whitespace();
        
        let tactic = self.tactic()?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Repeat,
            range,
            children: smallvec![tactic],
        })))
    }
    
    /// Parse `try` tactic combinator
    pub fn try_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("try")?;
        self.skip_whitespace();
        
        let tactic = self.tactic()?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Try,
            range,
            children: smallvec![tactic],
        })))
    }
    
    /// Parse `first` tactic combinator
    pub fn first_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("first")?;
        self.skip_whitespace();
        
        // first | tac1 | tac2 | ...
        let mut tactics = Vec::new();
        
        // Expect at least one tactic
        self.expect_char('|')?;
        self.skip_whitespace();
        tactics.push(self.tactic()?);
        
        // Parse additional alternatives
        while self.peek() == Some('|') {
            self.advance(); // consume '|'
            self.skip_whitespace();
            tactics.push(self.tactic()?);
            self.skip_whitespace();
        }
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::First,
            range,
            children: tactics.into(),
        })))
    }
    
    /// Parse `all_goals` tactic combinator
    pub fn all_goals_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("all_goals")?;
        self.skip_whitespace();
        
        let tactic = self.tactic()?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::AllGoals,
            range,
            children: smallvec![tactic],
        })))
    }
    
    /// Parse `any_goals` tactic combinator
    pub fn any_goals_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("any_goals")?;
        self.skip_whitespace();
        
        let tactic = self.tactic()?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::AllGoals, // Reuse AllGoals for now
            range,
            children: smallvec![tactic],
        })))
    }
    
    /// Parse `focus` tactic combinator
    pub fn focus_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("focus")?;
        self.skip_whitespace();
        
        let tactic = self.tactic()?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Focus,
            range,
            children: smallvec![tactic],
        })))
    }
    
    /// Parse `fail_if_success` tactic
    pub fn fail_if_success_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("fail_if_success")?;
        self.skip_whitespace();
        
        let tactic = self.tactic()?;
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::CustomTactic, // Use CustomTactic for now
            range,
            children: smallvec![tactic],
        })))
    }
    
    /// Parse `guard` tactics (guard_hyp, guard_target, guard_expr)
    pub fn guard_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        if self.peek_keyword("guard_hyp") {
            self.keyword("guard_hyp")?;
            self.skip_whitespace();
            
            // Parse hypothesis name
            let hyp = self.identifier()?;
            self.skip_whitespace();
            
            // Parse colon and type/value
            self.expect_char(':')?;
            self.skip_whitespace();
            
            let guard_expr = self.term()?;
            
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::CustomTactic,
                range,
                children: smallvec![hyp, guard_expr],
            })))
        } else if self.peek_keyword("guard_target") {
            self.keyword("guard_target")?;
            self.skip_whitespace();
            
            // Parse expected target
            let target = self.term()?;
            
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::CustomTactic,
                range,
                children: smallvec![target],
            })))
        } else if self.peek_keyword("guard_expr") {
            self.keyword("guard_expr")?;
            self.skip_whitespace();
            
            // Parse expression to check
            let expr = self.term()?;
            self.skip_whitespace();
            
            // Parse = and expected value
            self.expect_char('=')?;
            self.skip_whitespace();
            
            let expected = self.term()?;
            
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::CustomTactic,
                range,
                children: smallvec![expr, expected],
            })))
        } else {
            Err(ParseError::boxed(
                ParseErrorKind::Expected("guard tactic".to_string()),
                self.position(),
            ))
        }
    }
    
    /// Parse `conv` mode for conversion tactics
    pub fn conv_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("conv")?;
        self.skip_whitespace();
        
        // Optional at clause
        let target = if self.peek_keyword("at") {
            self.keyword("at")?;
            self.skip_whitespace();
            Some(self.identifier()?)
        } else {
            None
        };
        
        self.skip_whitespace();
        
        // Parse => and conversion tactics
        if self.peek() == Some('=') && self.input().peek_nth(1) == Some('>') {
            self.advance(); // consume '='
            self.advance(); // consume '>'
        } else if self.peek_keyword("in") {
            self.keyword("in")?;
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("=> or in".to_string()),
                self.position(),
            ));
        }
        
        self.skip_whitespace();
        
        // Parse conversion tactic sequence
        let conv_tactics = self.parse_conv_tactics()?;
        
        let range = self.input().range_from(start);
        let mut children = smallvec![];
        if let Some(t) = target {
            children.push(t);
        }
        children.push(conv_tactics);
        
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::CustomTactic,
            range,
            children,
        })))
    }
    
    /// Parse conversion tactics inside conv mode
    fn parse_conv_tactics(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut tactics = Vec::new();
        
        loop {
            self.skip_whitespace();
            
            // Check for conv-specific tactics
            if self.peek_keyword("lhs") {
                self.keyword("lhs")?;
                tactics.push(self.make_tactic_atom("lhs", start));
            } else if self.peek_keyword("rhs") {
                self.keyword("rhs")?;
                tactics.push(self.make_tactic_atom("rhs", start));
            } else if self.peek_keyword("arg") {
                self.keyword("arg")?;
                self.skip_whitespace();
                let n = self.number()?;
                tactics.push(n);
            } else if self.peek_keyword("ext") {
                self.keyword("ext")?;
                tactics.push(self.make_tactic_atom("ext", start));
            } else if self.peek_keyword("change") {
                self.keyword("change")?;
                self.skip_whitespace();
                let new_expr = self.term()?;
                tactics.push(new_expr);
            } else if self.peek_keyword("rw") || self.peek_keyword("rewrite") {
                tactics.push(self.rewrite_tactic()?);
            } else {
                // Try to parse a regular tactic
                match self.try_parse(|p| p.tactic()) {
                    Ok(tac) => tactics.push(tac),
                    Err(_) => break,
                }
            }
            
            self.skip_whitespace();
            
            // Check for semicolon separator
            if self.peek() == Some(';') {
                self.advance();
            } else if !self.peek_keyword("lhs") 
                   && !self.peek_keyword("rhs") 
                   && !self.peek_keyword("arg")
                   && !self.peek_keyword("ext")
                   && !self.peek_keyword("change")
                   && !self.peek_keyword("rw") {
                break;
            }
        }
        
        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::TacticSeq,
            range,
            children: tactics.into(),
        })))
    }
    
    /// Parse `suffices` tactic
    pub fn suffices_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        
        self.keyword("suffices")?;
        self.skip_whitespace();
        
        // Optional name
        let name = if self.peek().is_some_and(|c| c.is_alphabetic()) && !self.peek_keyword("by") {
            Some(self.identifier()?)
        } else {
            None
        };
        
        self.skip_whitespace();
        
        // Parse type
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.term()?;
        
        self.skip_whitespace();
        
        // Parse proof
        let proof = if self.peek_keyword("by") {
            self.by_tactic()?
        } else if self.peek_keyword("from") {
            self.keyword("from")?;
            self.skip_whitespace();
            self.term()?
        } else {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("by or from".to_string()),
                self.position(),
            ));
        };
        
        let range = self.input().range_from(start);
        let mut children = smallvec![];
        if let Some(n) = name {
            children.push(n);
        }
        children.push(ty);
        children.push(proof);
        
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::CustomTactic,
            range,
            children,
        })))
    }
    
    /// Helper to create an atom
    fn make_tactic_atom(&self, s: &str, start: lean_syn_expr::SourcePos) -> Syntax {
        let range = self.input().range_from(start);
        Syntax::Atom(lean_syn_expr::SyntaxAtom {
            range,
            value: eterned::BaseCoword::new(s),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    fn parse_tactic(input: &str) -> ParserResult<Syntax> {
        let mut parser = Parser::new(input);
        parser.with_mode(crate::parser::ParsingMode::Tactic, |p| p.tactic())
    }
    
    #[test]
    fn test_repeat_tactic() {
        let result = parse_tactic("repeat simp").unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::Repeat));
    }
    
    #[test]
    fn test_try_tactic() {
        let result = parse_tactic("try exact h").unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::Try));
    }
    
    #[test]
    fn test_first_tactic() {
        let result = parse_tactic("first | simp | rfl | assumption").unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::First));
    }
    
    #[test]
    fn test_all_goals_tactic() {
        let result = parse_tactic("all_goals simp").unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::AllGoals));
    }
}