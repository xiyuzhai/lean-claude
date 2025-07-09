use expect_test::{expect, Expect};
use lean_parser::Parser;

fn check_parse(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    match parser.module() {
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
fn test_empty_module() {
    check_parse(
        "",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Module,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                    },
                    children: [],
                },
            )"#]],
    );
}

#[test]
fn test_import() {
    check_parse(
        "import Mathlib.Data.Nat.Basic",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Module,
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 1,
                            offset: 0,
                        },
                        end: SourcePos {
                            line: 1,
                            column: 30,
                            offset: 29,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: Import,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 1,
                                        offset: 0,
                                    },
                                    end: SourcePos {
                                        line: 1,
                                        column: 30,
                                        offset: 29,
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
                                                    column: 30,
                                                    offset: 29,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Mathlib.Data.Nat.Basic",
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
fn test_def_command() {
    check_parse(
        "def foo : Nat := 42",
        expect![[r#"
            Node(
                SyntaxNode {
                    kind: Module,
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
                                kind: Def,
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
                                                    column: 8,
                                                    offset: 7,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "foo",
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
                                                    column: 14,
                                                    offset: 13,
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
                                                    column: 18,
                                                    offset: 17,
                                                },
                                                end: SourcePos {
                                                    line: 1,
                                                    column: 20,
                                                    offset: 19,
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
