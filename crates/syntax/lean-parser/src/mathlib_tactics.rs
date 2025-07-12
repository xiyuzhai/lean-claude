//! Common Mathlib tactics implementation
//!
//! This module implements tactics commonly used in Mathlib4

use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    parser::{Parser, ParserResult},
};

impl<'a> Parser<'a> {
    /// Parse `ring` tactic - solves goals about commutative (semi)rings
    pub fn ring_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("ring")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            smallvec![],
        ))))
    }

    /// Parse `ring_nf` tactic - normalizes ring expressions
    pub fn ring_nf_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("ring_nf")?;
        self.skip_whitespace();

        // Optional location
        let location = self.parse_tactic_location()?;

        let range = self.input().range_from(start);
        let mut children = smallvec![];
        if let Some(loc) = location {
            children.push(loc);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            children,
        ))))
    }

    /// Parse `linarith` tactic - linear arithmetic solver
    pub fn linarith_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("linarith")?;
        self.skip_whitespace();

        // Optional arguments [h1, h2, ...]
        let args = if self.peek() == Some('[') {
            self.advance(); // consume '['
            self.skip_whitespace();

            let mut hyps = Vec::new();
            while self.peek() != Some(']') {
                hyps.push(self.term()?);
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
            Some(hyps)
        } else {
            None
        };

        let range = self.input().range_from(start);
        let children = args.unwrap_or_default().into();

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            children,
        ))))
    }

    /// Parse `simp_all` tactic
    pub fn simp_all_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("simp_all")?;
        self.skip_whitespace();

        // Parse optional simp arguments
        let (only, lemmas, config) = self.parse_simp_args()?;

        let range = self.input().range_from(start);
        let mut children = smallvec![];

        if only {
            children.push(self.make_atom("only", start));
        }
        children.extend(lemmas);
        if let Some(cfg) = config {
            children.push(cfg);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            children,
        ))))
    }

    /// Parse `norm_num` tactic - numerical normalization
    pub fn norm_num_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("norm_num")?;
        self.skip_whitespace();

        // Optional location
        let location = self.parse_tactic_location()?;

        let range = self.input().range_from(start);
        let mut children = smallvec![];
        if let Some(loc) = location {
            children.push(loc);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            children,
        ))))
    }

    /// Parse `field_simp` tactic
    pub fn field_simp_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("field_simp")?;
        self.skip_whitespace();

        // Parse optional simp arguments
        let (only, lemmas, _config) = self.parse_simp_args()?;

        let range = self.input().range_from(start);
        let mut children = smallvec![];

        if only {
            children.push(self.make_atom("only", start));
        }
        children.extend(lemmas);

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            children,
        ))))
    }

    /// Parse `abel` tactic - for abelian group problems
    pub fn abel_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("abel")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            smallvec![],
        ))))
    }

    /// Parse `omega` tactic - for linear integer/natural arithmetic
    pub fn omega_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("omega")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            smallvec![],
        ))))
    }

    /// Parse `tauto` tactic - tautology prover
    pub fn tauto_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("tauto")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            smallvec![],
        ))))
    }

    /// Parse `aesop` tactic - general automation
    pub fn aesop_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("aesop")?;
        self.skip_whitespace();

        // Optional configuration
        let config = if self.peek() == Some('(') {
            self.advance(); // consume '('
            self.skip_whitespace();

            let mut options = Vec::new();
            while self.peek() != Some(')') {
                options.push(self.identifier()?);
                self.skip_whitespace();

                if self.peek() == Some(',') {
                    self.advance();
                    self.skip_whitespace();
                }
            }

            self.expect_char(')')?;
            Some(options)
        } else {
            None
        };

        let range = self.input().range_from(start);
        let children = config.unwrap_or_default().into();

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            children,
        ))))
    }

    /// Parse `hint` tactic
    pub fn hint_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("hint")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            smallvec![],
        ))))
    }

    /// Parse `library_search` tactic
    pub fn library_search_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("library_search")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            smallvec![],
        ))))
    }

    /// Parse `suggest` tactic
    pub fn suggest_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("suggest")?;
        self.skip_whitespace();

        // Optional depth
        let depth = if self.peek().is_some_and(|c| c.is_ascii_digit()) {
            Some(self.number()?)
        } else {
            None
        };

        let range = self.input().range_from(start);
        let mut children = smallvec![];
        if let Some(d) = depth {
            children.push(d);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            children,
        ))))
    }

    /// Parse tactic location: `at h1 h2 ⊢` or `at *`
    fn parse_tactic_location(&mut self) -> ParserResult<Option<Syntax>> {
        if !self.peek_keyword("at") {
            return Ok(None);
        }

        let start = self.position();
        self.keyword("at")?;
        self.skip_whitespace();

        let mut targets = Vec::new();

        if self.peek() == Some('*') {
            self.advance();
            targets.push(self.make_atom("*", start));
        } else {
            // Parse hypothesis names and ⊢
            loop {
                if self.peek() == Some('⊢')
                    || (self.peek() == Some('|') && self.input().peek_nth(1) == Some('-'))
                {
                    self.advance(); // consume ⊢ or |
                    if self.peek() == Some('-') {
                        self.advance(); // consume -
                    }
                    targets.push(self.make_atom("⊢", self.position()));
                } else if self.peek().is_some_and(|c| c.is_alphabetic()) {
                    targets.push(self.identifier()?);
                } else {
                    break;
                }
                self.skip_whitespace();
            }
        }

        if targets.is_empty() {
            return Err(ParseError::boxed(
                ParseErrorKind::Expected("location".to_string()),
                self.position(),
            ));
        }

        let range = self.input().range_from(start);
        Ok(Some(Syntax::Node(Box::new(SyntaxNode::new(
            SyntaxKind::CustomTactic,
            range,
            targets.into(),
        )))))
    }

    /// Helper to create an atom
    fn make_atom(&self, s: &str, start: lean_syn_expr::SourcePos) -> Syntax {
        let range = self.input().range_from(start);
        Syntax::Atom(lean_syn_expr::SyntaxAtom::new(
            range,
            eterned::BaseCoword::new(s),
        ))
    }

    /// Parse simp arguments: optional only, lemmas, and config
    fn parse_simp_args(&mut self) -> ParserResult<(bool, Vec<Syntax>, Option<Syntax>)> {
        let mut only = false;
        let mut lemmas = Vec::new();
        let mut config = None;

        // Check for "only"
        if self.peek_keyword("only") {
            self.keyword("only")?;
            only = true;
            self.skip_whitespace();
        }

        // Parse lemmas: [lemma1, -lemma2, ↑lemma3, ...]
        if self.peek() == Some('[') {
            self.advance(); // consume '['
            self.skip_whitespace();

            while self.peek() != Some(']') {
                // Check for - (remove lemma)
                let remove = if self.peek() == Some('-') {
                    self.advance();
                    true
                } else {
                    false
                };

                // Check for ↑ (simp!)
                let exclaim = if self.peek() == Some('↑') {
                    self.advance();
                    true
                } else {
                    false
                };

                self.skip_whitespace();
                let lemma = self.term()?;

                // Wrap lemma with modifiers if needed
                let lemma_node = if remove || exclaim {
                    let start = self.position();
                    let range = self.input().range_from(start);
                    let mut children = smallvec![];
                    if remove {
                        children.push(self.make_atom("-", start));
                    }
                    if exclaim {
                        children.push(self.make_atom("↑", start));
                    }
                    children.push(lemma);

                    Syntax::Node(Box::new(SyntaxNode::new(
                        SyntaxKind::CustomTactic,
                        range,
                        children,
                    )))
                } else {
                    lemma
                };

                lemmas.push(lemma_node);
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
        }

        // Parse config: (config := { ... })
        if self.peek() == Some('(') {
            self.input_mut().save_position();
            self.advance(); // consume '('
            self.skip_whitespace();

            if self.peek_keyword("config") {
                self.keyword("config")?;
                self.skip_whitespace();

                if self.peek() == Some(':') && self.input().peek_nth(1) == Some('=') {
                    self.advance(); // ':'
                    self.advance(); // '='
                    self.skip_whitespace();

                    // For now, just consume the config as a term
                    config = Some(self.term()?);

                    self.skip_whitespace();
                    self.expect_char(')')?;
                    self.input_mut().commit_position();
                } else {
                    self.input_mut().restore_position();
                }
            } else {
                self.input_mut().restore_position();
            }
        }

        Ok((only, lemmas, config))
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
    fn test_ring_tactic() {
        let result = parse_tactic("ring").unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::CustomTactic));
    }

    #[test]
    fn test_linarith_tactic() {
        let result = parse_tactic("linarith").unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::CustomTactic));

        let result = parse_tactic("linarith [h1, h2]").unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::CustomTactic));
    }

    #[test]
    fn test_simp_all_tactic() {
        let result = parse_tactic("simp_all").unwrap();
        assert!(matches!(result, Syntax::Node(node) if node.kind == SyntaxKind::CustomTactic));
    }
}
