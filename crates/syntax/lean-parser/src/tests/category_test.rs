use expect_test::{expect, Expect};

use crate::Parser;

fn check_parse(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let result = parser.term();

    match result {
        Ok(syntax) => {
            let output = format!("{syntax:#?}");
            expected.assert_eq(&output);
        }
        Err(err) => {
            let diagnostic = err.to_diagnostic();
            let output = format!("Error: {diagnostic:#?}");
            expected.assert_eq(&output);
        }
    }
}

#[test]
#[ignore] // TODO: Fix category system
fn test_category_lambda() {
    check_parse(
        "λ x => x + 1",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Lambda,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 13,
                            offset: 13,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 3,
                                        offset: 3,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 4,
                                    },
                                },
                                value: BaseCoword {
                                    data: "x",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: BinOp,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 8,
                                        offset: 8,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 13,
                                        offset: 13,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 8,
                                                    offset: 8,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 9,
                                                    offset: 9,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "x",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 10,
                                                    offset: 10,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 11,
                                                    offset: 11,
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
                                                    column: 12,
                                                    offset: 12,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 13,
                                                    offset: 13,
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
                    ],
                },
            )"#]],
    );
}

#[test]
#[ignore] // TODO: Fix category system
fn test_category_error_message() {
    check_parse(
        "λ => x",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Lambda,
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
                                        offset: 6,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 7,
                                        offset: 7,
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
