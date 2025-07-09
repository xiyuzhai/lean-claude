use expect_test::{expect, Expect};

use crate::parser::Parser;

fn check_module(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    match parser.module() {
        Ok(syntax) => expected.assert_eq(&format!("{:#?}", syntax)),
        Err(e) => expected.assert_eq(&format!("Error: {}", e)),
    }
}

#[test]
fn test_empty_module() {
    check_module(
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
fn test_import_statement() {
    check_module(
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
fn test_multiple_imports() {
    check_module(
        r#"import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic"#,
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
                            line: 2,
                            column: 27,
                            offset: 56,
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
                        Node(
                            SyntaxNode {
                                kind: Import,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 1,
                                        offset: 30,
                                    },
                                    end: SourcePos {
                                        line: 2,
                                        column: 27,
                                        offset: 56,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 2,
                                                    column: 8,
                                                    offset: 37,
                                                },
                                                end: SourcePos {
                                                    line: 2,
                                                    column: 27,
                                                    offset: 56,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Mathlib.Logic.Basic",
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
fn test_namespace_and_end() {
    check_module(
        r#"namespace Nat
end Nat"#,
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
                            line: 2,
                            column: 8,
                            offset: 21,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: Namespace,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 1,
                                        column: 1,
                                        offset: 0,
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
                                                    column: 14,
                                                    offset: 13,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Nat",
                                            },
                                        },
                                    ),
                                ],
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: End,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 1,
                                        offset: 14,
                                    },
                                    end: SourcePos {
                                        line: 2,
                                        column: 8,
                                        offset: 21,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 2,
                                                    column: 5,
                                                    offset: 18,
                                                },
                                                end: SourcePos {
                                                    line: 2,
                                                    column: 8,
                                                    offset: 21,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Nat",
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
fn test_comments_and_whitespace() {
    check_module(
        r#"-- Copyright header
/- Block comment -/

import Mathlib.Data.Nat.Basic

-- Some comment
open Nat"#,
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
                            line: 7,
                            column: 9,
                            offset: 96,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: Import,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 4,
                                        column: 1,
                                        offset: 41,
                                    },
                                    end: SourcePos {
                                        line: 4,
                                        column: 30,
                                        offset: 70,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 4,
                                                    column: 8,
                                                    offset: 48,
                                                },
                                                end: SourcePos {
                                                    line: 4,
                                                    column: 30,
                                                    offset: 70,
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
                        Node(
                            SyntaxNode {
                                kind: Open,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 7,
                                        column: 1,
                                        offset: 88,
                                    },
                                    end: SourcePos {
                                        line: 7,
                                        column: 9,
                                        offset: 96,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 7,
                                                    column: 6,
                                                    offset: 93,
                                                },
                                                end: SourcePos {
                                                    line: 7,
                                                    column: 9,
                                                    offset: 96,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Nat",
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
