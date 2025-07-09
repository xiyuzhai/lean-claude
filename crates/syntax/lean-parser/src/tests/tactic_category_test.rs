use crate::Parser;
use expect_test::{expect, Expect};

fn check_parse(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let result = parser.by_tactic();
    
    match result {
        Ok(syntax) => {
            let output = format!("{:#?}", syntax);
            expected.assert_eq(&output);
        }
        Err(err) => {
            let output = format!("Error: {}", err);
            expected.assert_eq(&output);
        }
    }
}

#[test]
fn test_exact_tactic() {
    check_parse(
        "by exact h",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: By,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 11,
                            offset: 10,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: Exact,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 3,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 11,
                                        offset: 10,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 10,
                                                    offset: 9,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 11,
                                                    offset: 10,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "h",
                                            },
                                        },
                                    ),
                                ],
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_tactic_sequence() {
    check_parse(
        "by intro x; exact x",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: By,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 20,
                            offset: 19,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: TacticSeq,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 3,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 20,
                                        offset: 19,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: Intro,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 4,
                                                    offset: 3,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 11,
                                                    offset: 10,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 10,
                                                                offset: 9,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 11,
                                                                offset: 10,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "x",
                                                        },
                                                    },
                                                ),
                                            ],
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: Exact,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 13,
                                                    offset: 12,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 20,
                                                    offset: 19,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 19,
                                                                offset: 18,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 20,
                                                                offset: 19,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "x",
                                                        },
                                                    },
                                                ),
                                            ],
                                        },
                                    ),
                                ],
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_tactic_alternative() {
    check_parse(
        "by simp <|> rfl",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: By,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 16,
                            offset: 15,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: TacticAlt,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 3,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 16,
                                        offset: 15,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: Simp,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 4,
                                                    offset: 3,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 9,
                                                    offset: 8,
                                                },
                                            },
                                            children: [],
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: Rfl,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 13,
                                                    offset: 12,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 16,
                                                    offset: 15,
                                                },
                                            },
                                            children: [],
                                        },
                                    ),
                                ],
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_simp_with_lemmas() {
    check_parse(
        "by simp [h1, h2, -h3]",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: By,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 22,
                            offset: 21,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: Simp,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 3,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 22,
                                        offset: 21,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 10,
                                                    offset: 9,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 12,
                                                    offset: 11,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "h1",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 14,
                                                    offset: 13,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 16,
                                                    offset: 15,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "h2",
                                            },
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: SimpExclude,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 18,
                                                    offset: 17,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 21,
                                                    offset: 20,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 19,
                                                                offset: 18,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 21,
                                                                offset: 20,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "h3",
                                                        },
                                                    },
                                                ),
                                            ],
                                        },
                                    ),
                                ],
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_rewrite_tactic() {
    check_parse(
        "by rw [h1, ←h2]",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: By,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 16,
                            offset: 17,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: Rewrite,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 3,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 16,
                                        offset: 17,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 8,
                                                    offset: 7,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 10,
                                                    offset: 9,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "h1",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 4,
                                                    offset: 3,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 13,
                                                    offset: 14,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "←",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 13,
                                                    offset: 14,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 15,
                                                    offset: 16,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "h2",
                                            },
                                        },
                                    ),
                                ],
                            },
                        ),
                    ],
                },
            )"#]],
    );
}