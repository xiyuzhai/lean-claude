use expect_test::{expect, Expect};
use lean_parser::Parser;

fn check_parse(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    match parser.term() {
        Ok(result) => expected.assert_eq(&format!("{result:#?}")),
        Err(e) => panic!("Parse error: {e}"),
    }
}

#[test]
fn test_sort_type_prop() {
    // Sort with level
    check_parse(
        "Sort u",
        expect![[r#"
        Node(
            SyntaxNode {
                kind: Sort,
                range: SourceRange {
                    start: SourcePos {
                        line: 1,
                        column: 1,
                        offset: 0,
                    },
                    end: SourcePos {
                        line: 1,
                        column: 7,
                        offset: 7,
                    },
                },
                children: [
                    Atom(
                        SyntaxAtom {
                            range: SourceRange {
                                start: SourcePos {
                                    line: 1,
                                    column: 6,
                                    offset: 5,
                                },
                                end: SourcePos {
                                    line: 1,
                                    column: 7,
                                    offset: 7,
                                },
                            },
                            value: BaseCoword {
                                data: "u",
                            },
                        },
                    ),
                ],
            },
        )"#]],
    );

    // Type*
    check_parse(
        "Type*",
        expect![[r#"
        Node(
            SyntaxNode {
                kind: Type,
                range: SourceRange {
                    start: SourcePos {
                        line: 1,
                        column: 1,
                        offset: 0,
                    },
                    end: SourcePos {
                        line: 1,
                        column: 6,
                        offset: 6,
                    },
                },
                children: [
                    Atom(
                        SyntaxAtom {
                            range: SourceRange {
                                start: SourcePos {
                                    line: 1,
                                    column: 5,
                                    offset: 4,
                                },
                                end: SourcePos {
                                    line: 1,
                                    column: 6,
                                    offset: 6,
                                },
                            },
                            value: BaseCoword {
                                data: "*",
                            },
                        },
                    ),
                ],
            },
        )"#]],
    );

    // Prop
    check_parse(
        "Prop",
        expect![[r#"
        Node(
            SyntaxNode {
                kind: Prop,
                range: SourceRange {
                    start: SourcePos {
                        line: 1,
                        column: 1,
                        offset: 0,
                    },
                    end: SourcePos {
                        line: 1,
                        column: 5,
                        offset: 4,
                    },
                },
                children: [],
            },
        )"#]],
    );
}

#[test]
fn test_implicit_with_type() {
    // This test checks that Type in implicit binders works correctly
    check_parse(
        "{α : Type}",
        expect![[r#"
        Node(
            SyntaxNode {
                kind: LeftBrace,
                range: SourceRange {
                    start: SourcePos {
                        line: 1,
                        column: 1,
                        offset: 0,
                    },
                    end: SourcePos {
                        line: 1,
                        column: 11,
                        offset: 11,
                    },
                },
                children: [
                    Atom(
                        SyntaxAtom {
                            range: SourceRange {
                                start: SourcePos {
                                    line: 1,
                                    column: 2,
                                    offset: 1,
                                },
                                end: SourcePos {
                                    line: 1,
                                    column: 3,
                                    offset: 3,
                                },
                            },
                            value: BaseCoword {
                                data: "α",
                            },
                        },
                    ),
                    Node(
                        SyntaxNode {
                            kind: Type,
                            range: SourceRange {
                                start: SourcePos {
                                    line: 1,
                                    column: 6,
                                    offset: 6,
                                },
                                end: SourcePos {
                                    line: 1,
                                    column: 10,
                                    offset: 10,
                                },
                            },
                            children: [],
                        },
                    ),
                ],
            },
        )"#]],
    );
}

#[test]
fn test_function_with_universes() {
    check_parse(
        "(α : Type u) → Type v",
        expect![[r#"
        Node(
            SyntaxNode {
                kind: Arrow,
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
                            kind: LeftParen,
                            range: SourceRange {
                                start: SourcePos {
                                    line: 1,
                                    column: 1,
                                    offset: 0,
                                },
                                end: SourcePos {
                                    line: 1,
                                    column: 13,
                                    offset: 12,
                                },
                            },
                            children: [
                                Atom(
                                    SyntaxAtom {
                                        range: SourceRange {
                                            start: SourcePos {
                                                line: 1,
                                                column: 2,
                                                offset: 1,
                                            },
                                            end: SourcePos {
                                                line: 1,
                                                column: 3,
                                                offset: 2,
                                            },
                                        },
                                        value: BaseCoword {
                                            data: "α",
                                        },
                                    },
                                ),
                                Node(
                                    SyntaxNode {
                                        kind: Type,
                                        range: SourceRange {
                                            start: SourcePos {
                                                line: 1,
                                                column: 6,
                                                offset: 5,
                                            },
                                            end: SourcePos {
                                                line: 1,
                                                column: 12,
                                                offset: 11,
                                            },
                                        },
                                        children: [
                                            Atom(
                                                SyntaxAtom {
                                                    range: SourceRange {
                                                        start: SourcePos {
                                                            line: 1,
                                                            column: 11,
                                                            offset: 10,
                                                        },
                                                        end: SourcePos {
                                                            line: 1,
                                                            column: 12,
                                                            offset: 11,
                                                        },
                                                    },
                                                    value: BaseCoword {
                                                        data: "u",
                                                    },
                                                },
                                            ),
                                        ],
                                    },
                                ),
                            ],
                        },
                    ),
                    Node(
                        SyntaxNode {
                            kind: Type,
                            range: SourceRange {
                                start: SourcePos {
                                    line: 1,
                                    column: 16,
                                    offset: 15,
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
                                            data: "v",
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
fn test_universe_max_imax() {
    check_parse(
        "Type (max u v)",
        expect![[r#"
        Node(
            SyntaxNode {
                kind: Type,
                range: SourceRange {
                    start: SourcePos {
                        line: 1,
                        column: 1,
                        offset: 0,
                    },
                    end: SourcePos {
                        line: 1,
                        column: 15,
                        offset: 14,
                    },
                },
                children: [
                    Node(
                        SyntaxNode {
                            kind: UniverseMax,
                            range: SourceRange {
                                start: SourcePos {
                                    line: 1,
                                    column: 7,
                                    offset: 6,
                                },
                                end: SourcePos {
                                    line: 1,
                                    column: 14,
                                    offset: 13,
                                },
                            },
                            children: [
                                Atom(
                                    SyntaxAtom {
                                        range: SourceRange {
                                            start: SourcePos {
                                                line: 1,
                                                column: 11,
                                                offset: 10,
                                            },
                                            end: SourcePos {
                                                line: 1,
                                                column: 12,
                                                offset: 11,
                                            },
                                        },
                                        value: BaseCoword {
                                            data: "u",
                                        },
                                    },
                                ),
                                Atom(
                                    SyntaxAtom {
                                        range: SourceRange {
                                            start: SourcePos {
                                                line: 1,
                                                column: 13,
                                                offset: 12,
                                            },
                                            end: SourcePos {
                                                line: 1,
                                                column: 14,
                                                offset: 13,
                                            },
                                        },
                                        value: BaseCoword {
                                            data: "v",
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
