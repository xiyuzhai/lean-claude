use crate::Parser;
use expect_test::{expect, Expect};

fn check_parse(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let result = parser.command();
    
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
                            column: 31,
                            offset: 32,
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
        expect!["Error: expected => at SourcePos { line: 1, column: 17, offset: 16 }"],
    );
}

#[test]
fn test_macro_with_attributes() {
    check_parse(
        r#"@[simp] macro "test" : term => `(1)"#,
        expect!["Error: expected command at SourcePos { line: 1, column: 1, offset: 0 }"],
    );
}