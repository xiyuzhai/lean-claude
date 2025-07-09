use crate::Parser;
use expect_test::{expect, Expect};

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
fn test_lambda_variations() {
    // λ syntax
    check_parse(
        "λ x => x",
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
                            column: 9,
                            offset: 9,
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
                    ],
                },
            )"#]],
    );

    // backslash syntax
    check_parse(
        "\\x => x",
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
                            column: 8,
                            offset: 7,
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
                                    data: "x",
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
                                    data: "x",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );

    // fun syntax
    check_parse(
        "fun x => x",
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
            )"#]],
    );
}

#[test]
fn test_forall_variations() {
    // ∀ syntax
    check_parse(
        "∀ x, x = x",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Forall,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 11,
                            offset: 12,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 3,
                                        offset: 4,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 4,
                                        offset: 5,
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
                                        column: 6,
                                        offset: 7,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 11,
                                        offset: 12,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 6,
                                                    offset: 7,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 7,
                                                    offset: 8,
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
                                                    column: 8,
                                                    offset: 9,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 9,
                                                    offset: 10,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "=",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 10,
                                                    offset: 11,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 11,
                                                    offset: 12,
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
            )"#]],
    );

    // forall keyword syntax
    check_parse(
        "forall x, x = x",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Forall,
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
                                        column: 9,
                                        offset: 8,
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
                                        column: 11,
                                        offset: 10,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 16,
                                        offset: 15,
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
                                                data: "x",
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
                                                data: "=",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 15,
                                                    offset: 14,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 16,
                                                    offset: 15,
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
            )"#]],
    );
}

#[test]
fn test_let_expression() {
    check_parse(
        "let x := 5 in x + 1",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Let,
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
                                        offset: 9,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 11,
                                        offset: 10,
                                    },
                                },
                                value: BaseCoword {
                                    data: "5",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: BinOp,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 15,
                                        offset: 14,
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
                                                    column: 15,
                                                    offset: 14,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 16,
                                                    offset: 15,
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
                                                    column: 17,
                                                    offset: 16,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 18,
                                                    offset: 17,
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
fn test_have_expression() {
    check_parse(
        "have h : P := proof",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Have,
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
                                    data: "h",
                                },
                            },
                        ),
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
                                    data: "P",
                                },
                            },
                        ),
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 15,
                                        offset: 14,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 20,
                                        offset: 19,
                                    },
                                },
                                value: BaseCoword {
                                    data: "proof",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_show_expression() {
    check_parse(
        "show P from proof",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Show,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 18,
                            offset: 17,
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
                                    data: "P",
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
                                        column: 18,
                                        offset: 17,
                                    },
                                },
                                value: BaseCoword {
                                    data: "proof",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_parentheses() {
    check_parse(
        "(x + y)",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: BinOp,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 2,
                            offset: 1,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 7,
                            offset: 6,
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
                                    data: "x",
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
                                    data: "y",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_implicit_arguments() {
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
                                        column: 10,
                                        offset: 10,
                                    },
                                },
                                value: BaseCoword {
                                    data: "Type",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_instance_implicit() {
    check_parse(
        "[Monad m]",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: LeftBracket,
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
                                        column: 2,
                                        offset: 1,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 7,
                                        offset: 6,
                                    },
                                },
                                value: BaseCoword {
                                    data: "Monad",
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
                                        column: 9,
                                        offset: 8,
                                    },
                                },
                                value: BaseCoword {
                                    data: "m",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_operator_precedence() {
    // Test that * binds tighter than +
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
fn test_arrow_type() {
    check_parse(
        "α → β",
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
                            column: 6,
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
                                        offset: 2,
                                    },
                                },
                                value: BaseCoword {
                                    data: "α",
                                },
                            },
                        ),
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
                                        offset: 6,
                                    },
                                },
                                value: BaseCoword {
                                    data: "→",
                                },
                            },
                        ),
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 5,
                                        offset: 7,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 6,
                                        offset: 9,
                                    },
                                },
                                value: BaseCoword {
                                    data: "β",
                                },
                            },
                        ),
                    ],
                },
            )"#]],
    );
}

#[test]
fn test_complex_expression() {
    check_parse(
        "λ f g x => f (g x)",
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
                            column: 19,
                            offset: 19,
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
                                    data: "f",
                                },
                            },
                        ),
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 5,
                                        offset: 5,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 6,
                                        offset: 6,
                                    },
                                },
                                value: BaseCoword {
                                    data: "g",
                                },
                            },
                        ),
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 7,
                                        offset: 7,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 8,
                                        offset: 8,
                                    },
                                },
                                value: BaseCoword {
                                    data: "x",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: App,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 12,
                                        offset: 12,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 19,
                                        offset: 19,
                                    },
                                },
                                children: [
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
                                                data: "f",
                                            },
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: App,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 1,
                                                    column: 15,
                                                    offset: 15,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 18,
                                                    offset: 18,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 15,
                                                                offset: 15,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 16,
                                                                offset: 16,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "g",
                                                        },
                                                    },
                                                ),
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 1,
                                                                column: 17,
                                                                offset: 17,
                                                            },
                                                            end: SourcePos {
                                                                line: 1,
                                                                column: 18,
                                                                offset: 18,
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