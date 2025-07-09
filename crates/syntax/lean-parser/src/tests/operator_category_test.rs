use crate::Parser;
use expect_test::{expect, Expect};

fn check_parse(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let result = parser.term();
    
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
fn test_unary_operators_category() {
    // Negation
    check_parse(
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
    
    // Logical not
    check_parse(
        "!p",
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
                                    data: "!",
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
                                    data: "p",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_binary_operators_category() {
    // All operators through category system
    check_parse(
        "a + b * c",
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
                                                data: "b",
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

#[test]
fn test_mixed_operators() {
    check_parse(
        "-a + b",
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
                            column: 7,
                            offset: 6,
                        },
                    },
                    children: [
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
                                        column: 4,
                                        offset: 3,
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
                                                data: "a",
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
                                        column: 4,
                                        offset: 3,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 5,
                                        offset: 4,
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
                    ],
                },
            )"#]],
    );
}