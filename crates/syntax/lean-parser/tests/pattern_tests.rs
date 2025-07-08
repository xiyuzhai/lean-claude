use lean_parser::Parser;
use expect_test::{expect, Expect};

fn check_term(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    match parser.term() {
        Ok(syntax) => {
            let output = format!("{:#?}", syntax);
            expected.assert_eq(&output);
        }
        Err(err) => {
            let output = format!("Error: {:?}", err);
            expected.assert_eq(&output);
        }
    }
}

#[test]
fn test_match_simple() {
    check_term(
        "match x with | true => 1 | false => 0",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Match,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 38,
                            offset: 37,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 7,
                                        offset: 6,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 8,
                                        offset: 7,
                                    },
                                },
                                value: BaseCoword {
                                    data: "x",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: MatchArm,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 16,
                                        offset: 15,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 26,
                                        offset: 25,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 16,
                                                    offset: 15,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 20,
                                                    offset: 19,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "true",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 24,
                                                    offset: 23,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 25,
                                                    offset: 24,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "1",
                                            },
                                        },
                                    ),
                                ],
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: MatchArm,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 28,
                                        offset: 27,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 38,
                                        offset: 37,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 28,
                                                    offset: 27,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 33,
                                                    offset: 32,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "false",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 37,
                                                    offset: 36,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 38,
                                                    offset: 37,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "0",
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
fn test_match_wildcard() {
    check_term(
        "match x with | Some y => y | _ => 0",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Match,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 36,
                            offset: 35,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 7,
                                        offset: 6,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 8,
                                        offset: 7,
                                    },
                                },
                                value: BaseCoword {
                                    data: "x",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: MatchArm,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 16,
                                        offset: 15,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 28,
                                        offset: 27,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: ConstructorPattern,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 16,
                                                    offset: 15,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 23,
                                                    offset: 22,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 16,
                                                                offset: 15,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 20,
                                                                offset: 19,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "Some",
                                                        },
                                                    },
                                                ),
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 21,
                                                                offset: 20,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 22,
                                                                offset: 21,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "y",
                                                        },
                                                    },
                                                ),
                                            ],
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 26,
                                                    offset: 25,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 27,
                                                    offset: 26,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "y",
                                            },
                                        },
                                    ),
                                ],
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: MatchArm,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 30,
                                        offset: 29,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 36,
                                        offset: 35,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: WildcardPattern,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 30,
                                                    offset: 29,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 31,
                                                    offset: 30,
                                                },
                                            },
                                            children: [],
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 35,
                                                    offset: 34,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 36,
                                                    offset: 35,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "0",
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