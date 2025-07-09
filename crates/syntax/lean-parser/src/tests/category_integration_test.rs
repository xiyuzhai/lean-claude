#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use crate::Parser;

    fn check_parse_module(input: &str, expected: Expect) {
        let mut parser = Parser::new(input);
        let result = parser.module();

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
    fn test_category_system_integration() {
        let module_text = r#"
import Mathlib.Data.List.Basic

namespace Example

def myFunction (x : Nat) : Nat := x + 1

theorem myTheorem : myFunction 5 = 6 := by
  simp [myFunction]
  rfl

#check myFunction
#eval myFunction 10

end Example
"#;

        check_parse_module(
            module_text,
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
                            line: 16,
                            column: 1,
                            offset: 214,
                        },
                    },
                    children: [
                        Node(
                            SyntaxNode {
                                kind: Import,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 2,
                                        column: 1,
                                        offset: 1,
                                    },
                                    end: SourcePos {
                                        line: 2,
                                        column: 31,
                                        offset: 31,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 2,
                                                    column: 8,
                                                    offset: 8,
                                                },
                                                end: SourcePos {
                                                    line: 2,
                                                    column: 31,
                                                    offset: 31,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Mathlib.Data.List.Basic",
                                            },
                                        },
                                    ),
                                ],
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: Namespace,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 4,
                                        column: 1,
                                        offset: 33,
                                    },
                                    end: SourcePos {
                                        line: 4,
                                        column: 18,
                                        offset: 50,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 4,
                                                    column: 11,
                                                    offset: 43,
                                                },
                                                end: SourcePos {
                                                    line: 4,
                                                    column: 18,
                                                    offset: 50,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Example",
                                            },
                                        },
                                    ),
                                ],
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: Def,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 6,
                                        column: 1,
                                        offset: 52,
                                    },
                                    end: SourcePos {
                                        line: 8,
                                        column: 1,
                                        offset: 93,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 6,
                                                    column: 5,
                                                    offset: 56,
                                                },
                                                end: SourcePos {
                                                    line: 6,
                                                    column: 15,
                                                    offset: 66,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "myFunction",
                                            },
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: LeftParen,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 6,
                                                    column: 16,
                                                    offset: 67,
                                                },
                                                end: SourcePos {
                                                    line: 6,
                                                    column: 25,
                                                    offset: 76,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 6,
                                                                column: 17,
                                                                offset: 68,
                                                            },
                                                            end: SourcePos {
                                                                line: 6,
                                                                column: 18,
                                                                offset: 69,
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
                                                                line: 6,
                                                                column: 21,
                                                                offset: 72,
                                                            },
                                                            end: SourcePos {
                                                                line: 6,
                                                                column: 24,
                                                                offset: 75,
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
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 6,
                                                    column: 28,
                                                    offset: 79,
                                                },
                                                end: SourcePos {
                                                    line: 6,
                                                    column: 31,
                                                    offset: 82,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Nat",
                                            },
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: BinOp,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 6,
                                                    column: 35,
                                                    offset: 86,
                                                },
                                                end: SourcePos {
                                                    line: 8,
                                                    column: 1,
                                                    offset: 93,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 6,
                                                                column: 35,
                                                                offset: 86,
                                                            },
                                                            end: SourcePos {
                                                                line: 6,
                                                                column: 36,
                                                                offset: 87,
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
                                                                line: 6,
                                                                column: 37,
                                                                offset: 88,
                                                            },
                                                            end: SourcePos {
                                                                line: 6,
                                                                column: 38,
                                                                offset: 89,
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
                                                                line: 6,
                                                                column: 39,
                                                                offset: 90,
                                                            },
                                                            end: SourcePos {
                                                                line: 6,
                                                                column: 40,
                                                                offset: 91,
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
                        ),
                        Node(
                            SyntaxNode {
                                kind: Theorem,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 8,
                                        column: 1,
                                        offset: 93,
                                    },
                                    end: SourcePos {
                                        line: 12,
                                        column: 1,
                                        offset: 163,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 8,
                                                    column: 9,
                                                    offset: 101,
                                                },
                                                end: SourcePos {
                                                    line: 8,
                                                    column: 18,
                                                    offset: 110,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "myTheorem",
                                            },
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: BinOp,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 8,
                                                    column: 21,
                                                    offset: 113,
                                                },
                                                end: SourcePos {
                                                    line: 8,
                                                    column: 38,
                                                    offset: 130,
                                                },
                                            },
                                            children: [
                                                Node(
                                                    SyntaxNode {
                                                        kind: App,
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 8,
                                                                column: 21,
                                                                offset: 113,
                                                            },
                                                            end: SourcePos {
                                                                line: 8,
                                                                column: 34,
                                                                offset: 126,
                                                            },
                                                        },
                                                        children: [
                                                            Atom(
                                                                SyntaxAtom {
                                                                    range: SourceRange {
                                                                        start: SourcePos {
                                                                            line: 8,
                                                                            column: 21,
                                                                            offset: 113,
                                                                        },
                                                                        end: SourcePos {
                                                                            line: 8,
                                                                            column: 31,
                                                                            offset: 123,
                                                                        },
                                                                    },
                                                                    value: BaseCoword {
                                                                        data: "myFunction",
                                                                    },
                                                                },
                                                            ),
                                                            Atom(
                                                                SyntaxAtom {
                                                                    range: SourceRange {
                                                                        start: SourcePos {
                                                                            line: 8,
                                                                            column: 32,
                                                                            offset: 124,
                                                                        },
                                                                        end: SourcePos {
                                                                            line: 8,
                                                                            column: 33,
                                                                            offset: 125,
                                                                        },
                                                                    },
                                                                    value: BaseCoword {
                                                                        data: "5",
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
                                                                line: 8,
                                                                column: 34,
                                                                offset: 126,
                                                            },
                                                            end: SourcePos {
                                                                line: 8,
                                                                column: 35,
                                                                offset: 127,
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
                                                                line: 8,
                                                                column: 36,
                                                                offset: 128,
                                                            },
                                                            end: SourcePos {
                                                                line: 8,
                                                                column: 37,
                                                                offset: 129,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "6",
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
                                                    line: 8,
                                                    column: 41,
                                                    offset: 133,
                                                },
                                                end: SourcePos {
                                                    line: 12,
                                                    column: 1,
                                                    offset: 163,
                                                },
                                            },
                                            children: [
                                                Node(
                                                    SyntaxNode {
                                                        kind: By,
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 8,
                                                                column: 41,
                                                                offset: 133,
                                                            },
                                                            end: SourcePos {
                                                                line: 10,
                                                                column: 3,
                                                                offset: 158,
                                                            },
                                                        },
                                                        children: [
                                                            Node(
                                                                SyntaxNode {
                                                                    kind: Simp,
                                                                    range: SourceRange {
                                                                        start: SourcePos {
                                                                            line: 9,
                                                                            column: 3,
                                                                            offset: 138,
                                                                        },
                                                                        end: SourcePos {
                                                                            line: 9,
                                                                            column: 20,
                                                                            offset: 155,
                                                                        },
                                                                    },
                                                                    children: [
                                                                        Atom(
                                                                            SyntaxAtom {
                                                                                range: SourceRange {
                                                                                    start: SourcePos {
                                                                                        line: 9,
                                                                                        column: 9,
                                                                                        offset: 144,
                                                                                    },
                                                                                    end: SourcePos {
                                                                                        line: 9,
                                                                                        column: 19,
                                                                                        offset: 154,
                                                                                    },
                                                                                },
                                                                                value: BaseCoword {
                                                                                    data: "myFunction",
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
                                                                line: 10,
                                                                column: 3,
                                                                offset: 158,
                                                            },
                                                            end: SourcePos {
                                                                line: 10,
                                                                column: 6,
                                                                offset: 161,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "rfl",
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
                                kind: HashCheck,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 12,
                                        column: 1,
                                        offset: 163,
                                    },
                                    end: SourcePos {
                                        line: 13,
                                        column: 1,
                                        offset: 181,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 12,
                                                    column: 2,
                                                    offset: 164,
                                                },
                                                end: SourcePos {
                                                    line: 12,
                                                    column: 7,
                                                    offset: 169,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "check",
                                            },
                                        },
                                    ),
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 12,
                                                    column: 8,
                                                    offset: 170,
                                                },
                                                end: SourcePos {
                                                    line: 12,
                                                    column: 18,
                                                    offset: 180,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "myFunction",
                                            },
                                        },
                                    ),
                                ],
                            },
                        ),
                        Node(
                            SyntaxNode {
                                kind: HashEval,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 13,
                                        column: 1,
                                        offset: 181,
                                    },
                                    end: SourcePos {
                                        line: 15,
                                        column: 1,
                                        offset: 202,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 13,
                                                    column: 2,
                                                    offset: 182,
                                                },
                                                end: SourcePos {
                                                    line: 13,
                                                    column: 6,
                                                    offset: 186,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "eval",
                                            },
                                        },
                                    ),
                                    Node(
                                        SyntaxNode {
                                            kind: App,
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 13,
                                                    column: 7,
                                                    offset: 187,
                                                },
                                                end: SourcePos {
                                                    line: 15,
                                                    column: 1,
                                                    offset: 202,
                                                },
                                            },
                                            children: [
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 13,
                                                                column: 7,
                                                                offset: 187,
                                                            },
                                                            end: SourcePos {
                                                                line: 13,
                                                                column: 17,
                                                                offset: 197,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "myFunction",
                                                        },
                                                    },
                                                ),
                                                Atom(
                                                    SyntaxAtom {
                                                        range: SourceRange {
                                                            start: SourcePos {
                                                                line: 13,
                                                                column: 18,
                                                                offset: 198,
                                                            },
                                                            end: SourcePos {
                                                                line: 13,
                                                                column: 20,
                                                                offset: 200,
                                                            },
                                                        },
                                                        value: BaseCoword {
                                                            data: "10",
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
                                kind: End,
                                range: SourceRange {
                                    start: SourcePos {
                                        line: 15,
                                        column: 1,
                                        offset: 202,
                                    },
                                    end: SourcePos {
                                        line: 15,
                                        column: 12,
                                        offset: 213,
                                    },
                                },
                                children: [
                                    Atom(
                                        SyntaxAtom {
                                            range: SourceRange {
                                                start: SourcePos {
                                                    line: 15,
                                                    column: 5,
                                                    offset: 206,
                                                },
                                                end: SourcePos {
                                                    line: 15,
                                                    column: 12,
                                                    offset: 213,
                                                },
                                            },
                                            value: BaseCoword {
                                                data: "Example",
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
    fn test_error_recovery_suggestions() {
        // Test missing 'by' in tactic proof - actually this parses 'simp' as an
        // identifier which is valid syntax, just not what the user intended
        let result = Parser::new("theorem foo : True := simp").theorem_command();
        assert!(result.is_ok()); // This is actually valid syntax

        // Test missing command keyword at command level (not module level)
        let result = Parser::new("myDef := 42").command();
        assert!(result.is_err());

        // Test incomplete theorem
        let result = Parser::new("theorem foo : True :=").theorem_command();
        assert!(result.is_err());

        // Test tactic without 'by'
        let result = Parser::new("exact h").term();
        assert!(result.is_ok()); // This parses as function application
    }
}
