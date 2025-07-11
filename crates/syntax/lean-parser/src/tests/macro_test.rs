use expect_test::{expect, Expect};

use crate::Parser;

fn check_parse(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let result = parser.command();

    match result {
        Ok(syntax) => {
            let output = format!("{syntax:#?}");
            expected.assert_eq(&output);
        }
        Err(err) => {
            let output = format!("Error: {err}");
            expected.assert_eq(&output);
        }
    }
}

#[test]
fn test_simple_macro() {
    check_parse(
        r#"macro "myMacro" : term => `(42)"#,
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: MacroDef,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 32,
                            offset: 31,
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
                                        column: 16,
                                        offset: 15,
                                    },
                                },
                                value: BaseCoword {
                                    data: "myMacro",
                                },
                            },
                        ),
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
                                        column: 23,
                                        offset: 22,
                                    },
                                },
                                value: BaseCoword {
                                    data: "term",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: SyntaxQuotation,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 27,
                                        offset: 26,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 32,
                                        offset: 31,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 29,
                                                    offset: 28,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 31,
                                                    offset: 30,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "42",
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
fn test_notation() {
    check_parse(
        r#"notation "x ∈ S" => Membership.mem x S"#,
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: NotationDef,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 39,
                            offset: 40,
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
                                        column: 17,
                                        offset: 18,
                                    },
                                },
                                value: BaseCoword {
                                    data: "x ∈ S",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: App,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 31,
                                        offset: 32,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 39,
                                        offset: 40,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 21,
                                                    offset: 22,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 31,
                                                    offset: 32,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Membership",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 32,
                                                    offset: 33,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 35,
                                                    offset: 36,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "mem",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 36,
                                                    offset: 37,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 37,
                                                    offset: 38,
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
                                                    column: 38,
                                                    offset: 39,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 39,
                                                    offset: 40,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "S",
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
fn test_syntax_declaration() {
    check_parse(
        r#"syntax "while" term "do" term : term"#,
        expect!["Error: expected ':' at SourcePos { line: 1, column: 16, offset: 15 }"],
    );
}

#[test]
fn test_macro_with_antiquotation() {
    check_parse(
        r#"macro "double" x:term : term => `($x + $x)"#,
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: MacroDef,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 43,
                            offset: 42,
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
                                        column: 15,
                                        offset: 14,
                                    },
                                },
                                value: BaseCoword {
                                    data: "double",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: App,
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
                                                    column: 16,
                                                    offset: 15,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 17,
                                                    offset: 16,
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
                                                    column: 18,
                                                    offset: 17,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 22,
                                                    offset: 21,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "term",
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
                                        column: 25,
                                        offset: 24,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 29,
                                        offset: 28,
                                    },
                                },
                                value: BaseCoword {
                                    data: "term",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: SyntaxQuotation,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 33,
                                        offset: 32,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 43,
                                        offset: 42,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: BinOp,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 35,
                                                    offset: 34,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 42,
                                                    offset: 41,
                                                },
                                            },
                                            children: [
                                                Node(
                                                    SyntaxNode {
                                                        kind: SyntaxAntiquotation,
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 35,
                                                                offset: 34,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 37,
                                                                offset: 36,
                                                            },
                                                        },
                                                        children: [
                                                            Atom(
                                                                SyntaxAtom {
                                                                    range: SourceRange {
                                                                        start: SourcePos {
                                                                            line: 1,
                                                                            column: 36,
                                                                            offset: 35,
                                                                        },
                                                                        end: SourcePos {
                                                                            line: 1,
                                                                            column: 37,
                                                                            offset: 36,
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
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 38,
                                                                offset: 37,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 39,
                                                                offset: 38,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "+",
                                                        },
                                                    },
                                                ),
                                                Node(
                                                    SyntaxNode {
                                                        kind: SyntaxAntiquotation,
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 40,
                                                                offset: 39,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 42,
                                                                offset: 41,
                                                            },
                                                        },
                                                        children: [
                                                            Atom(
                                                                SyntaxAtom {
                                                                    range: SourceRange {
                                                                        start: SourcePos {
                                                                            line: 1,
                                                                            column: 41,
                                                                            offset: 40,
                                                                        },
                                                                        end: SourcePos {
                                                                            line: 1,
                                                                            column: 42,
                                                                            offset: 41,
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
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_macro_with_attributes() {
    check_parse(
        r#"@[simp] macro "test" : term => `(1)"#,
        expect!["Error: expected command at SourcePos { line: 1, column: 1, offset: 0 }"],
    );
}
