use expect_test::{expect, Expect};
use lean_parser::Parser;

fn check_term(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    match parser.term() {
        Ok(syntax) => {
            let output = format!("{syntax:#?}");
            expected.assert_eq(&output);
        }
        Err(err) => {
            let output = format!("Error: {err:?}");
            expected.assert_eq(&output);
        }
    }
}

#[test]
fn test_binary_operators() {
    check_term(
        "1 + 2",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: BinOp,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 6,
                            offset: 5,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 1,
                                        offset: 0,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 2,
                                        offset: 1,
                                    },
                                },
                                value: BaseCoword {
                                    data: "1",
                                },
                            },
                        ),
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 3,
                                        offset: 2,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 3,
                                    },
                                },
                                value: BaseCoword {
                                    data: "+",
                                },
                            },
                        ),
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
                                        offset: 5,
                                    },
                                },
                                value: BaseCoword {
                                    data: "2",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_precedence() {
    check_term(
        "1 + 2 * 3",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: BinOp,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 10,
                            offset: 9,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 1,
                                        offset: 0,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 2,
                                        offset: 1,
                                    },
                                },
                                value: BaseCoword {
                                    data: "1",
                                },
                            },
                        ),
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 3,
                                        offset: 2,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 3,
                                    },
                                },
                                value: BaseCoword {
                                    data: "+",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: BinOp,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 5,
                                        offset: 4,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 10,
                                        offset: 9,
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
                                                    offset: 5,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "2",
                                            },
                                        },
                                    ),
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
                                                data: "*",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 9,
                                                    offset: 8,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 10,
                                                    offset: 9,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "3",
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
fn test_unary_operators() {
    check_term(
        "-x",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: UnaryOp,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 3,
                            offset: 2,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 1,
                                        offset: 0,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 2,
                                        offset: 1,
                                    },
                                },
                                value: BaseCoword {
                                    data: "-",
                                },
                            },
                        ),
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
                                    data: "x",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_arrow_operator() {
    check_term(
        "Nat -> Bool",
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
                                        column: 1,
                                        offset: 0,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 3,
                                    },
                                },
                                value: BaseCoword {
                                    data: "Nat",
                                },
                            },
                        ),
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
                                        column: 7,
                                        offset: 6,
                                    },
                                },
                                value: BaseCoword {
                                    data: "->",
                                },
                            },
                        ),
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
                                        column: 12,
                                        offset: 11,
                                    },
                                },
                                value: BaseCoword {
                                    data: "Bool",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_right_associative() {
    check_term(
        "a -> b -> c",
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
                                        column: 1,
                                        offset: 0,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 2,
                                        offset: 1,
                                    },
                                },
                                value: BaseCoword {
                                    data: "a",
                                },
                            },
                        ),
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 3,
                                        offset: 2,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 5,
                                        offset: 4,
                                    },
                                },
                                value: BaseCoword {
                                    data: "->",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: Arrow,
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
                                                    column: 6,
                                                    offset: 5,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 7,
                                                    offset: 6,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "b",
                                            },
                                        },
                                    ),
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
                                                data: "->",
                                            },
                                        },
                                    ),
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
                                                data: "c",
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
