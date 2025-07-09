//! Tactic parsing for Lean 4

use lean_syn_expr::{Syntax, SyntaxAtom, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    error::{ParseError, ParseErrorKind},
    lexical::is_id_start,
    parser::{Parser, ParserResult, ParsingMode},
};

impl<'a> Parser<'a> {
    /// Parse a tactic block: `by tactic`
    pub fn by_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("by")?;
        self.skip_whitespace();

        // Switch to tactic mode for parsing the tactic
        let tactic = self.with_mode(ParsingMode::Tactic, |p| p.tactic())?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::By,
            range,
            children: smallvec![tactic],
        })))
    }

    /// Parse a single tactic or tactic sequence
    pub fn tactic(&mut self) -> ParserResult<Syntax> {
        self.tactic_seq()
    }

    /// Parse a tactic sequence (tactics separated by `;` or `<|>`)
    pub fn tactic_seq(&mut self) -> ParserResult<Syntax> {
        let start = self.position();
        let mut tactics = vec![self.tactic_atom()?];

        loop {
            self.skip_whitespace();

            if self.peek() == Some(';') {
                // Sequential composition
                self.advance();
                self.skip_whitespace();

                // Allow trailing semicolon
                if self.peek_tactic_end() {
                    break;
                }

                tactics.push(self.tactic_atom()?);
            } else if self.peek() == Some('<')
                && self.input().peek_nth(1) == Some('|')
                && self.input().peek_nth(2) == Some('>')
            {
                // Alternative composition
                self.advance(); // <
                self.advance(); // |
                self.advance(); // >
                self.skip_whitespace();

                let right = self.tactic_atom()?;
                let left = if tactics.len() == 1 {
                    tactics.into_iter().next().unwrap()
                } else {
                    let left_range = self.input().range_from(start);
                    Syntax::Node(Box::new(SyntaxNode {
                        kind: SyntaxKind::TacticSeq,
                        range: left_range,
                        children: tactics.into(),
                    }))
                };

                let range = self.input().range_from(start);
                return Ok(Syntax::Node(Box::new(SyntaxNode {
                    kind: SyntaxKind::TacticAlt,
                    range,
                    children: smallvec![left, right],
                })));
            } else {
                break;
            }
        }

        if tactics.len() == 1 {
            Ok(tactics.into_iter().next().unwrap())
        } else {
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::TacticSeq,
                range,
                children: tactics.into(),
            })))
        }
    }

    /// Parse atomic tactic
    pub fn tactic_atom(&mut self) -> ParserResult<Syntax> {
        self.skip_whitespace();

        // Check for tactic combinators first
        if self.peek_keyword("repeat") {
            return self.repeat_tactic();
        }
        if self.peek_keyword("try") {
            return self.try_tactic();
        }
        if self.peek_keyword("first") {
            return self.first_tactic();
        }
        if self.peek_keyword("all_goals") {
            return self.all_goals_tactic();
        }
        if self.peek_keyword("focus") {
            return self.focus_tactic();
        }

        // Check for specific tactics
        if self.peek_keyword("exact") {
            return self.exact_tactic();
        }
        if self.peek_keyword("apply") {
            return self.apply_tactic();
        }
        if self.peek_keyword("intro") {
            return self.intro_tactic();
        }
        if self.peek_keyword("intros") {
            return self.intros_tactic();
        }
        if self.peek_keyword("cases") {
            return self.cases_tactic();
        }
        if self.peek_keyword("induction") {
            return self.induction_tactic();
        }
        if self.peek_keyword("simp") {
            return self.simp_tactic();
        }
        if self.peek_keyword("rw") || self.peek_keyword("rewrite") {
            return self.rewrite_tactic();
        }
        if self.peek_keyword("rfl") {
            return self.rfl_tactic();
        }
        if self.peek_keyword("sorry") {
            return self.sorry_tactic();
        }
        if self.peek_keyword("assumption") {
            return self.assumption_tactic();
        }
        if self.peek_keyword("contradiction") {
            return self.contradiction_tactic();
        }
        if self.peek_keyword("calc") {
            return self.calc_tactic();
        }
        if self.peek_keyword("have") {
            return self.have_tactic();
        }
        if self.peek_keyword("let") {
            return self.let_tactic();
        }
        if self.peek_keyword("show") {
            return self.show_tactic();
        }

        // Parenthesized tactic or custom tactic
        if self.peek() == Some('(') {
            return self.paren_tactic();
        }

        // Default: parse as custom tactic (identifier with optional arguments)
        self.custom_tactic()
    }

    /// Parse exact tactic: `exact term`
    fn exact_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("exact")?;
        self.skip_whitespace();

        let term = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Exact,
            range,
            children: smallvec![term],
        })))
    }

    /// Parse apply tactic: `apply term`
    fn apply_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("apply")?;
        self.skip_whitespace();

        let term = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Apply,
            range,
            children: smallvec![term],
        })))
    }

    /// Parse intro tactic: `intro name`
    fn intro_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("intro")?;
        self.skip_whitespace();

        let name = if self.peek().is_some_and(is_id_start) {
            Some(self.identifier()?)
        } else {
            None
        };

        let range = self.input().range_from(start);
        let children = if let Some(n) = name {
            smallvec![n]
        } else {
            smallvec![]
        };

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Intro,
            range,
            children,
        })))
    }

    /// Parse intros tactic: `intros [names]`
    fn intros_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("intros")?;
        self.skip_whitespace();

        let mut names = Vec::new();
        while self.peek().is_some_and(is_id_start) {
            names.push(self.identifier()?);
            self.skip_whitespace();
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Intros,
            range,
            children: names.into(),
        })))
    }

    /// Parse cases tactic: `cases term [with pattern*]`
    fn cases_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("cases")?;
        self.skip_whitespace();

        let term = self.term()?;
        self.skip_whitespace();

        let mut children = smallvec![term];

        if self.peek_keyword("with") {
            self.keyword("with")?;
            self.skip_whitespace();

            // Parse case patterns
            while !self.peek_tactic_end() {
                children.push(self.case_pattern()?);
                self.skip_whitespace();

                if self.peek() == Some('|') {
                    self.advance();
                    self.skip_whitespace();
                } else {
                    break;
                }
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Cases,
            range,
            children,
        })))
    }

    /// Parse induction tactic: `induction term [with pattern*] [generalizing
    /// ident*]`
    fn induction_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("induction")?;
        self.skip_whitespace();

        let term = self.term()?;
        self.skip_whitespace();

        let mut children = smallvec![term];

        if self.peek_keyword("with") {
            self.keyword("with")?;
            self.skip_whitespace();

            // Parse induction patterns
            while !self.peek_tactic_end() && !self.peek_keyword("generalizing") {
                children.push(self.case_pattern()?);
                self.skip_whitespace();

                if self.peek() == Some('|') {
                    self.advance();
                    self.skip_whitespace();
                } else {
                    break;
                }
            }
        }

        if self.peek_keyword("generalizing") {
            self.keyword("generalizing")?;
            self.skip_whitespace();

            while self.peek().is_some_and(is_id_start) {
                children.push(self.identifier()?);
                self.skip_whitespace();
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Induction,
            range,
            children,
        })))
    }

    /// Parse simp tactic: `simp [args]`
    fn simp_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("simp")?;
        self.skip_whitespace();

        let mut children = smallvec![];

        // Parse optional simp lemmas in brackets
        if self.peek() == Some('[') {
            self.advance();
            self.skip_whitespace();

            while self.peek() != Some(']') {
                children.push(self.simp_arg()?);
                self.skip_whitespace();

                if self.peek() == Some(',') {
                    self.advance();
                    self.skip_whitespace();
                } else if self.peek() != Some(']') {
                    return Err(ParseError::new(
                        ParseErrorKind::Expected(", or ]".to_string()),
                        self.position(),
                    ));
                }
            }

            self.expect_char(']')?;
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Simp,
            range,
            children,
        })))
    }

    /// Parse rewrite tactic: `rw [lemmas]` or `rewrite [lemmas]`
    fn rewrite_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        if self.peek_keyword("rw") {
            self.keyword("rw")?;
        } else {
            self.keyword("rewrite")?;
        }
        self.skip_whitespace();

        let mut children = smallvec![];

        // Parse rewrite lemmas in brackets
        self.expect_char('[')?;
        self.skip_whitespace();

        while self.peek() != Some(']') {
            // Optional ← for reverse rewrite
            if self.peek() == Some('←')
                || (self.peek() == Some('<') && self.input().peek_nth(1) == Some('-'))
            {
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
            }

            children.push(self.term()?);
            self.skip_whitespace();

            if self.peek() == Some(',') {
                self.advance();
                self.skip_whitespace();
            } else if self.peek() != Some(']') {
                return Err(ParseError::new(
                    ParseErrorKind::Expected(", or ]".to_string()),
                    self.position(),
                ));
            }
        }

        self.expect_char(']')?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Rewrite,
            range,
            children,
        })))
    }

    /// Parse rfl tactic
    fn rfl_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("rfl")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Rfl,
            range,
            children: smallvec![],
        })))
    }

    /// Parse sorry tactic
    fn sorry_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("sorry")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Sorry,
            range,
            children: smallvec![],
        })))
    }

    /// Parse assumption tactic
    fn assumption_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("assumption")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Assumption,
            range,
            children: smallvec![],
        })))
    }

    /// Parse contradiction tactic
    fn contradiction_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("contradiction")?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Contradiction,
            range,
            children: smallvec![],
        })))
    }

    /// Parse calc tactic
    fn calc_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("calc")?;
        self.skip_whitespace();

        let mut steps = Vec::new();

        // First step
        let lhs = self.term()?;
        self.skip_whitespace();

        let rel = self.term()?; // relation operator
        self.skip_whitespace();

        let rhs = self.term()?;
        self.skip_whitespace();

        let proof = if self.peek_keyword("by") {
            self.by_tactic()?
        } else {
            self.expect_char(':')?;
            self.expect_char('=')?;
            self.skip_whitespace();
            self.term()?
        };

        steps.push(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::CalcStep,
            range: self.input().range_from(start),
            children: smallvec![lhs, rel, rhs, proof],
        })));

        // Additional steps
        self.skip_whitespace();
        while self.peek() == Some('_') {
            let step_start = self.position();
            self.advance(); // consume _
            self.skip_whitespace();

            let rel = self.term()?;
            self.skip_whitespace();

            let rhs = self.term()?;
            self.skip_whitespace();

            let proof = if self.peek_keyword("by") {
                self.by_tactic()?
            } else {
                self.expect_char(':')?;
                self.expect_char('=')?;
                self.skip_whitespace();
                self.term()?
            };

            steps.push(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::CalcStep,
                range: self.input().range_from(step_start),
                children: smallvec![rel, rhs, proof],
            })));
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Calc,
            range,
            children: steps.into(),
        })))
    }

    /// Parse have tactic: `have name : type := proof`
    fn have_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("have")?;
        self.skip_whitespace();

        let name = if self.peek().is_some_and(is_id_start) && !self.peek_keyword("this") {
            Some(self.identifier()?)
        } else {
            None
        };

        self.skip_whitespace();
        self.expect_char(':')?;
        self.skip_whitespace();

        let ty = self.term()?;
        self.skip_whitespace();

        let proof = if self.peek_keyword("by") {
            self.by_tactic()?
        } else {
            self.expect_char(':')?;
            self.expect_char('=')?;
            self.skip_whitespace();
            self.term()?
        };

        let range = self.input().range_from(start);
        let mut children = smallvec![];
        if let Some(n) = name {
            children.push(n);
        }
        children.push(ty);
        children.push(proof);

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::TacticHave,
            range,
            children,
        })))
    }

    /// Parse let tactic: `let name := value`
    fn let_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("let")?;
        self.skip_whitespace();

        let name = self.identifier()?;
        self.skip_whitespace();

        self.expect_char(':')?;
        self.expect_char('=')?;
        self.skip_whitespace();

        let value = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::TacticLet,
            range,
            children: smallvec![name, value],
        })))
    }

    /// Parse show tactic: `show type`
    fn show_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("show")?;
        self.skip_whitespace();

        let ty = self.term()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::TacticShow,
            range,
            children: smallvec![ty],
        })))
    }

    /// Parse repeat tactic: `repeat tactic`
    fn repeat_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("repeat")?;
        self.skip_whitespace();

        let tactic = self.tactic_atom()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Repeat,
            range,
            children: smallvec![tactic],
        })))
    }

    /// Parse try tactic: `try tactic`
    fn try_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("try")?;
        self.skip_whitespace();

        let tactic = self.tactic_atom()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Try,
            range,
            children: smallvec![tactic],
        })))
    }

    /// Parse first tactic: `first | tactic1 | tactic2 | ...`
    fn first_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("first")?;
        self.skip_whitespace();

        let mut tactics = Vec::new();

        // Expect at least one |
        self.expect_char('|')?;
        self.skip_whitespace();

        loop {
            tactics.push(self.tactic_atom()?);
            self.skip_whitespace();

            if self.peek() == Some('|') && !self.peek_tactic_end() {
                self.advance();
                self.skip_whitespace();
            } else {
                break;
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::First,
            range,
            children: tactics.into(),
        })))
    }

    /// Parse all_goals tactic: `all_goals tactic`
    fn all_goals_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("all_goals")?;
        self.skip_whitespace();

        let tactic = self.tactic_atom()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::AllGoals,
            range,
            children: smallvec![tactic],
        })))
    }

    /// Parse focus tactic: `focus tactic`
    fn focus_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        self.keyword("focus")?;
        self.skip_whitespace();

        let tactic = self.tactic_atom()?;

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::Focus,
            range,
            children: smallvec![tactic],
        })))
    }

    /// Parse parenthesized tactic: `(tactic)`
    fn paren_tactic(&mut self) -> ParserResult<Syntax> {
        self.expect_char('(')?;
        self.skip_whitespace();

        let tactic = self.tactic()?;

        self.skip_whitespace();
        self.expect_char(')')?;

        Ok(tactic)
    }

    /// Parse custom tactic (identifier with optional arguments)
    fn custom_tactic(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let name = self.identifier()?;
        self.skip_whitespace();

        let mut children = smallvec![name];

        // Parse optional arguments
        while !self.peek_tactic_end() && !self.peek_tactic_separator() {
            if let Ok(arg) = self.try_parse(|p| p.term()) {
                children.push(arg);
                self.skip_whitespace();
            } else {
                break;
            }
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::CustomTactic,
            range,
            children,
        })))
    }

    /// Parse case pattern for cases/induction
    fn case_pattern(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let constructor = self.identifier()?;
        self.skip_whitespace();

        let mut vars = vec![constructor];

        while self.peek().is_some_and(is_id_start) {
            vars.push(self.identifier()?);
            self.skip_whitespace();
        }

        let range = self.input().range_from(start);
        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::CasePattern,
            range,
            children: vars.into(),
        })))
    }

    /// Parse simp argument (can be a lemma name or -lemma to exclude)
    fn simp_arg(&mut self) -> ParserResult<Syntax> {
        let start = self.position();

        let exclude = if self.peek() == Some('-') {
            self.advance();
            true
        } else {
            false
        };

        let lemma = self.term()?;

        if exclude {
            let range = self.input().range_from(start);
            Ok(Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::SimpExclude,
                range,
                children: smallvec![lemma],
            })))
        } else {
            Ok(lemma)
        }
    }

    /// Check if we're at the end of a tactic
    fn peek_tactic_end(&self) -> bool {
        self.peek().is_none()
            || self.peek() == Some(';')
            || self.peek() == Some(')')
            || self.peek() == Some(']')
            || self.peek() == Some('}')
            || self.peek() == Some('|')
            || (self.peek() == Some('<') && self.input().peek_nth(1) == Some('|'))
    }

    /// Check if we're at a tactic separator
    fn peek_tactic_separator(&self) -> bool {
        self.peek() == Some(';')
            || (self.peek() == Some('<')
                && self.input().peek_nth(1) == Some('|')
                && self.input().peek_nth(2) == Some('>'))
    }
}
