use crate::Parser;
use expect_test::{expect, Expect};
use lean_syn_expr::SyntaxKind;

fn check_elab_rules(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    match parser.module() {
        Ok(module) => {
            let output = format!("{:#?}", module);
            expected.assert_eq(&output);
        }
        Err(e) => {
            expected.assert_eq(&format!("Error: {e}"));
        }
    }
}

#[test]
fn test_basic_elab_rules() {
    check_elab_rules(
        r#"
elab_rules : term
  | `(myterm) => `(42)
"#,
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
                line: 4,
                column: 1,
                offset: 46,
            },
        },
        children: [
            Node(
                SyntaxNode {
                    kind: ElabRules,
                    range: SourceRange {
                        start: SourcePos {
                            line: 2,
                            column: 1,
                            offset: 1,
                        },
                        end: SourcePos {
                            line: 3,
                            column: 25,
                            offset: 45,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 14,
                                        offset: 14,
                                    },
                                    end: SourcePos {
                                        line: 2,
                                        column: 18,
                                        offset: 18,
                                    },
                                },
                                value: BaseCoword {
                                    data: "term",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: ElabRulesList,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 1,
                                        offset: 1,
                                    },
                                    end: SourcePos {
                                        line: 3,
                                        column: 25,
                                        offset: 45,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: SyntaxQuotation,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 3,
                                                    column: 5,
                                                    offset: 25,
                                                },
                                                end: SourcePos {
                                                    line: 3,
                                                    column: 14,
                                                    offset: 34,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 7,
                                                                offset: 27,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 13,
                                                                offset: 33,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "myterm",
                                                        },
                                                    },
                                                ),
                                            ],
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: SyntaxQuotation,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 3,
                                                    column: 19,
                                                    offset: 39,
                                                },
                                                end: SourcePos {
                                                    line: 3,
                                                    column: 25,
                                                    offset: 45,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 21,
                                                                offset: 41,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 23,
                                                                offset: 43,
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
fn test_elab_rules_multiple_patterns() {
    check_elab_rules(
        r#"
elab_rules : tactic
  | `(tactic| mytac $x) => `(simp [$x])
  | `(tactic| mytac) => `(simp)
"#,
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
                line: 5,
                column: 1,
                offset: 92,
            },
        },
        children: [
            Node(
                SyntaxNode {
                    kind: ElabRules,
                    range: SourceRange {
                        start: SourcePos {
                            line: 2,
                            column: 1,
                            offset: 1,
                        },
                        end: SourcePos {
                            line: 4,
                            column: 33,
                            offset: 91,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 14,
                                        offset: 14,
                                    },
                                    end: SourcePos {
                                        line: 2,
                                        column: 20,
                                        offset: 20,
                                    },
                                },
                                value: BaseCoword {
                                    data: "tactic",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: ElabRulesList,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 1,
                                        offset: 1,
                                    },
                                    end: SourcePos {
                                        line: 4,
                                        column: 33,
                                        offset: 91,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: SyntaxQuotation,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 3,
                                                    column: 5,
                                                    offset: 27,
                                                },
                                                end: SourcePos {
                                                    line: 3,
                                                    column: 26,
                                                    offset: 48,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 7,
                                                                offset: 29,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 14,
                                                                offset: 36,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "tactic|",
                                                        },
                                                    },
                                                ),
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 15,
                                                                offset: 37,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 20,
                                                                offset: 42,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "mytac",
                                                        },
                                                    },
                                                ),
                                                Node(
                                                    SyntaxNode {
                                                        kind: SyntaxAntiquotation,
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 21,
                                                                offset: 43,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 25,
                                                                offset: 47,
                                                            },
                                                        },
                                                        children: [
                                                            Atom(
                                                                SyntaxAtom {
                                                                    range: SourceRange {
                                                                        start: SourcePos {
                                                                            line: 3,
                                                                            column: 23,
                                                                            offset: 45,
                                                                        },
                                                                        end: SourcePos {
                                                                            line: 3,
                                                                            column: 24,
                                                                            offset: 46,
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
                                    Node(
                                        SyntaxNode {
                                            kind: SyntaxQuotation,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 3,
                                                    column: 31,
                                                    offset: 53,
                                                },
                                                end: SourcePos {
                                                    line: 3,
                                                    column: 42,
                                                    offset: 64,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 33,
                                                                offset: 55,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 37,
                                                                offset: 59,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "simp",
                                                        },
                                                    },
                                                ),
                                                Node(
                                                    SyntaxNode {
                                                        kind: List,
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 38,
                                                                offset: 60,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 41,
                                                                offset: 63,
                                                            },
                                                        },
                                                        children: [
                                                            Node(
                                                                SyntaxNode {
                                                                    kind: SyntaxAntiquotation,
                                                                    range: SourceRange {
                                                                        start: SourcePos {
                                                                            line: 3,
                                                                            column: 39,
                                                                            offset: 61,
                                                                        },
                                                                        end: SourcePos {
                                                                            line: 3,
                                                                            column: 40,
                                                                            offset: 62,
                                                                        },
                                                                    },
                                                                    children: [
                                                                        Atom(
                                                                            SyntaxAtom {
                                                                                range: SourceRange {
                                                                                    start: SourcePos {
                                                                                        line: 3,
                                                                                        column: 39,
                                                                                        offset: 61,
                                                                                    },
                                                                                    end: SourcePos {
                                                                                        line: 3,
                                                                                        column: 40,
                                                                                        offset: 62,
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
                                    Node(
                                        SyntaxNode {
                                            kind: SyntaxQuotation,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 4,
                                                    column: 5,
                                                    offset: 70,
                                                },
                                                end: SourcePos {
                                                    line: 4,
                                                    column: 22,
                                                    offset: 87,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 4,
                                                                column: 7,
                                                                offset: 72,
                                                            },
                                                            end: SourcePos {
                                                                line: 4,
                                                                column: 14,
                                                                offset: 79,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "tactic|",
                                                        },
                                                    },
                                                ),
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 4,
                                                                column: 15,
                                                                offset: 80,
                                                            },
                                                            end: SourcePos {
                                                                line: 4,
                                                                column: 20,
                                                                offset: 85,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "mytac",
                                                        },
                                                    },
                                                ),
                                            ],
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: App,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 4,
                                                    column: 28,
                                                    offset: 90,
                                                },
                                                end: SourcePos {
                                                    line: 4,
                                                    column: 33,
                                                    offset: 91,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 4,
                                                                column: 28,
                                                                offset: 90,
                                                            },
                                                            end: SourcePos {
                                                                line: 4,
                                                                column: 33,
                                                                offset: 91,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "simp",
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
fn test_elab_rules_with_attributes() {
    check_elab_rules(
        r#"
@[term_elab myterm]
elab_rules : term
  | `(myterm) => `(42)
"#,
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
                line: 5,
                column: 1,
                offset: 66,
            },
        },
        children: [
            Node(
                SyntaxNode {
                    kind: ElabRules,
                    range: SourceRange {
                        start: SourcePos {
                            line: 2,
                            column: 1,
                            offset: 1,
                        },
                        end: SourcePos {
                            line: 4,
                            column: 25,
                            offset: 65,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: AttributeList,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 1,
                                        offset: 1,
                                    },
                                    end: SourcePos {
                                        line: 2,
                                        column: 19,
                                        offset: 19,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: Attribute,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 2,
                                                    column: 1,
                                                    offset: 1,
                                                },
                                                end: SourcePos {
                                                    line: 2,
                                                    column: 19,
                                                    offset: 19,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 2,
                                                                column: 3,
                                                                offset: 3,
                                                            },
                                                            end: SourcePos {
                                                                line: 2,
                                                                column: 12,
                                                                offset: 12,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "term_elab",
                                                        },
                                                    },
                                                ),
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 2,
                                                                column: 13,
                                                                offset: 13,
                                                            },
                                                            end: SourcePos {
                                                                line: 2,
                                                                column: 19,
                                                                offset: 19,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "myterm",
                                                        },
                                                    },
                                                ),
                                            ],
                                        },
                                    ),
                                ],
                            },
                        ),
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 3,
                                        column: 14,
                                        offset: 34,
                                    },
                                    end: SourcePos {
                                        line: 3,
                                        column: 18,
                                        offset: 38,
                                    },
                                },
                                value: BaseCoword {
                                    data: "term",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: ElabRulesList,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 1,
                                        offset: 1,
                                    },
                                    end: SourcePos {
                                        line: 4,
                                        column: 25,
                                        offset: 65,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: SyntaxQuotation,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 4,
                                                    column: 5,
                                                    offset: 45,
                                                },
                                                end: SourcePos {
                                                    line: 4,
                                                    column: 14,
                                                    offset: 54,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 4,
                                                                column: 7,
                                                                offset: 47,
                                                            },
                                                            end: SourcePos {
                                                                line: 4,
                                                                column: 13,
                                                                offset: 53,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "myterm",
                                                        },
                                                    },
                                                ),
                                            ],
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: SyntaxQuotation,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 4,
                                                    column: 19,
                                                    offset: 59,
                                                },
                                                end: SourcePos {
                                                    line: 4,
                                                    column: 25,
                                                    offset: 65,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 4,
                                                                column: 21,
                                                                offset: 61,
                                                            },
                                                            end: SourcePos {
                                                                line: 4,
                                                                column: 23,
                                                                offset: 63,
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
fn test_elab_rules_expected_type() {
    check_elab_rules(
        r#"
elab_rules : term <= expectedType
  | `(mycast $x) => pure x
"#,
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
                line: 4,
                column: 1,
                offset: 61,
            },
        },
        children: [
            Node(
                SyntaxNode {
                    kind: ElabRules,
                    range: SourceRange {
                        start: SourcePos {
                            line: 2,
                            column: 1,
                            offset: 1,
                        },
                        end: SourcePos {
                            line: 3,
                            column: 28,
                            offset: 60,
                        },
                    },
                    children: [
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 14,
                                        offset: 14,
                                    },
                                    end: SourcePos {
                                        line: 2,
                                        column: 18,
                                        offset: 18,
                                    },
                                },
                                value: BaseCoword {
                                    data: "term",
                                },
                            },
                        ),
                        Atom(
                            SyntaxAtom {
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 22,
                                        offset: 22,
                                    },
                                    end: SourcePos {
                                        line: 2,
                                        column: 34,
                                        offset: 34,
                                    },
                                },
                                value: BaseCoword {
                                    data: "expectedType",
                                },
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: ElabRulesList,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 1,
                                        offset: 1,
                                    },
                                    end: SourcePos {
                                        line: 3,
                                        column: 28,
                                        offset: 60,
                                    },
                                },
                                children: [
                                    Node(
                                        SyntaxNode {
                                            kind: SyntaxQuotation,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 3,
                                                    column: 5,
                                                    offset: 41,
                                                },
                                                end: SourcePos {
                                                    line: 3,
                                                    column: 17,
                                                    offset: 53,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 7,
                                                                offset: 43,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 13,
                                                                offset: 49,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "mycast",
                                                        },
                                                    },
                                                ),
                                                Node(
                                                    SyntaxNode {
                                                        kind: SyntaxAntiquotation,
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 14,
                                                                offset: 50,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 16,
                                                                offset: 52,
                                                            },
                                                        },
                                                        children: [
                                                            Atom(
                                                                SyntaxAtom {
                                                                    range: SourceRange {
                                                                        start: SourcePos {
                                                                            line: 3,
                                                                            column: 15,
                                                                            offset: 51,
                                                                        },
                                                                        end: SourcePos {
                                                                            line: 3,
                                                                            column: 16,
                                                                            offset: 52,
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
                                    Node(
                                        SyntaxNode {
                                            kind: App,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 3,
                                                    column: 22,
                                                    offset: 58,
                                                },
                                                end: SourcePos {
                                                    line: 3,
                                                    column: 28,
                                                    offset: 60,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 22,
                                                                offset: 58,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 26,
                                                                offset: 60,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "pure",
                                                        },
                                                    },
                                                ),
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 3,
                                                                column: 27,
                                                                offset: 60,
                                                            },
                                                            end: SourcePos {
                                                                line: 3,
                                                                column: 28,
                                                                offset: 60,
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