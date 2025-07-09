use expect_test::{expect, Expect};
use smallvec::{smallvec, SmallVec};

use super::*;

fn check_syntax_debug(syntax: &Syntax, expected: Expect) {
    let output = format!("{syntax:#?}");
    expected.assert_eq(&output);
}

fn check_syntax_kind_display(kind: SyntaxKind, expected: &str) {
    assert_eq!(kind.to_string(), expected);
}

#[test]
fn test_source_pos() {
    let pos = SourcePos {
        line: 10,
        column: 5,
        offset: 150,
    };

    assert_eq!(pos.line, 10);
    assert_eq!(pos.column, 5);
    assert_eq!(pos.offset, 150);

    // Test Copy trait
    let pos2 = pos;
    assert_eq!(pos, pos2);
}

#[test]
fn test_source_range() {
    let start = SourcePos {
        line: 1,
        column: 0,
        offset: 0,
    };
    let end = SourcePos {
        line: 1,
        column: 10,
        offset: 10,
    };
    let range = SourceRange { start, end };

    assert_eq!(range.start, start);
    assert_eq!(range.end, end);
}

#[test]
fn test_syntax_missing() {
    let syntax = Syntax::Missing;
    assert!(syntax.is_missing());
    assert_eq!(syntax.kind(), None);
    assert_eq!(syntax.as_str(), "");

    check_syntax_debug(
        &syntax,
        expect![[r#"
            Missing"#]],
    );
}

#[test]
fn test_syntax_atom() {
    let range = SourceRange {
        start: SourcePos {
            line: 1,
            column: 0,
            offset: 0,
        },
        end: SourcePos {
            line: 1,
            column: 3,
            offset: 3,
        },
    };
    let atom = SyntaxAtom {
        range,
        value: "foo".into(),
    };
    let syntax = Syntax::Atom(atom);

    assert!(!syntax.is_missing());
    assert_eq!(syntax.kind(), None);
    assert_eq!(syntax.as_str(), "foo");
    assert_eq!(syntax.range(), Some(&range));
}

#[test]
fn test_syntax_node_empty() {
    let range = SourceRange {
        start: SourcePos {
            line: 1,
            column: 0,
            offset: 0,
        },
        end: SourcePos {
            line: 1,
            column: 0,
            offset: 0,
        },
    };
    let node = SyntaxNode {
        kind: SyntaxKind::Module,
        range,
        children: SmallVec::new(),
    };
    let syntax = Syntax::Node(Box::new(node));

    assert!(!syntax.is_missing());
    assert_eq!(syntax.kind(), Some(SyntaxKind::Module));
    assert_eq!(syntax.as_str(), "");
    assert_eq!(syntax.range(), Some(&range));
}

#[test]
fn test_syntax_node_with_children() {
    let range = SourceRange {
        start: SourcePos {
            line: 1,
            column: 0,
            offset: 0,
        },
        end: SourcePos {
            line: 1,
            column: 10,
            offset: 10,
        },
    };

    let child1 = Syntax::Atom(SyntaxAtom {
        range: SourceRange {
            start: SourcePos {
                line: 1,
                column: 0,
                offset: 0,
            },
            end: SourcePos {
                line: 1,
                column: 3,
                offset: 3,
            },
        },
        value: "def".into(),
    });

    let child2 = Syntax::Atom(SyntaxAtom {
        range: SourceRange {
            start: SourcePos {
                line: 1,
                column: 4,
                offset: 4,
            },
            end: SourcePos {
                line: 1,
                column: 7,
                offset: 7,
            },
        },
        value: "foo".into(),
    });

    let node = SyntaxNode {
        kind: SyntaxKind::Declaration,
        range,
        children: smallvec![child1, child2],
    };
    let syntax = Syntax::Node(Box::new(node));

    assert!(!syntax.is_missing());
    assert_eq!(syntax.kind(), Some(SyntaxKind::Declaration));

    if let Syntax::Node(n) = &syntax {
        assert_eq!(n.children.len(), 2);
        assert_eq!(n.children[0].as_str(), "def");
        assert_eq!(n.children[1].as_str(), "foo");
    } else {
        panic!("Expected Node variant");
    }
}

#[test]
fn test_syntax_kind_display() {
    check_syntax_kind_display(SyntaxKind::Module, "module");
    check_syntax_kind_display(SyntaxKind::Declaration, "declaration");
    check_syntax_kind_display(SyntaxKind::Theorem, "theorem");
    check_syntax_kind_display(SyntaxKind::Identifier, "identifier");
    check_syntax_kind_display(SyntaxKind::Lambda, "lambda");
    check_syntax_kind_display(SyntaxKind::Forall, "forall");
    check_syntax_kind_display(SyntaxKind::Let, "let");
    check_syntax_kind_display(SyntaxKind::Match, "match");
    check_syntax_kind_display(SyntaxKind::NumLit, "number");
    check_syntax_kind_display(SyntaxKind::StringLit, "string");
    check_syntax_kind_display(SyntaxKind::Whitespace, "whitespace");
    check_syntax_kind_display(SyntaxKind::Error, "error");
}

#[test]
fn test_nested_syntax_tree() {
    // Build: def foo : Nat := 42
    let def_range = SourceRange {
        start: SourcePos {
            line: 1,
            column: 0,
            offset: 0,
        },
        end: SourcePos {
            line: 1,
            column: 20,
            offset: 20,
        },
    };

    let def_keyword = Syntax::Atom(SyntaxAtom {
        range: SourceRange {
            start: SourcePos {
                line: 1,
                column: 0,
                offset: 0,
            },
            end: SourcePos {
                line: 1,
                column: 3,
                offset: 3,
            },
        },
        value: "def".into(),
    });

    let ident = Syntax::Node(Box::new(SyntaxNode {
        kind: SyntaxKind::Identifier,
        range: SourceRange {
            start: SourcePos {
                line: 1,
                column: 4,
                offset: 4,
            },
            end: SourcePos {
                line: 1,
                column: 7,
                offset: 7,
            },
        },
        children: smallvec![Syntax::Atom(SyntaxAtom {
            range: SourceRange {
                start: SourcePos {
                    line: 1,
                    column: 4,
                    offset: 4
                },
                end: SourcePos {
                    line: 1,
                    column: 7,
                    offset: 7
                },
            },
            value: "foo".into(),
        })],
    }));

    let type_part = Syntax::Node(Box::new(SyntaxNode {
        kind: SyntaxKind::App,
        range: SourceRange {
            start: SourcePos {
                line: 1,
                column: 8,
                offset: 8,
            },
            end: SourcePos {
                line: 1,
                column: 14,
                offset: 14,
            },
        },
        children: smallvec![
            Syntax::Atom(SyntaxAtom {
                range: SourceRange {
                    start: SourcePos {
                        line: 1,
                        column: 8,
                        offset: 8
                    },
                    end: SourcePos {
                        line: 1,
                        column: 9,
                        offset: 9
                    },
                },
                value: ":".into(),
            }),
            Syntax::Node(Box::new(SyntaxNode {
                kind: SyntaxKind::Identifier,
                range: SourceRange {
                    start: SourcePos {
                        line: 1,
                        column: 10,
                        offset: 10
                    },
                    end: SourcePos {
                        line: 1,
                        column: 13,
                        offset: 13
                    },
                },
                children: smallvec![Syntax::Atom(SyntaxAtom {
                    range: SourceRange {
                        start: SourcePos {
                            line: 1,
                            column: 10,
                            offset: 10
                        },
                        end: SourcePos {
                            line: 1,
                            column: 13,
                            offset: 13
                        },
                    },
                    value: "Nat".into(),
                })],
            })),
        ],
    }));

    let def_node = SyntaxNode {
        kind: SyntaxKind::Declaration,
        range: def_range,
        children: smallvec![def_keyword, ident, type_part],
    };

    let syntax = Syntax::Node(Box::new(def_node));

    assert_eq!(syntax.kind(), Some(SyntaxKind::Declaration));
    assert_eq!(syntax.range(), Some(&def_range));

    if let Syntax::Node(node) = &syntax {
        assert_eq!(node.children.len(), 3);

        // Check first child is "def"
        assert_eq!(node.children[0].as_str(), "def");

        // Check second child is identifier node
        assert_eq!(node.children[1].kind(), Some(SyntaxKind::Identifier));

        // Check third child is app node
        assert_eq!(node.children[2].kind(), Some(SyntaxKind::App));
    } else {
        panic!("Expected Node variant");
    }
}

#[test]
fn test_syntax_equality() {
    let pos1 = SourcePos {
        line: 1,
        column: 0,
        offset: 0,
    };
    let pos2 = SourcePos {
        line: 1,
        column: 3,
        offset: 3,
    };
    let range = SourceRange {
        start: pos1,
        end: pos2,
    };

    let atom1 = Syntax::Atom(SyntaxAtom {
        range,
        value: "foo".into(),
    });

    let atom2 = Syntax::Atom(SyntaxAtom {
        range,
        value: "foo".into(),
    });

    let atom3 = Syntax::Atom(SyntaxAtom {
        range,
        value: "bar".into(),
    });

    assert_eq!(atom1, atom2);
    assert_ne!(atom1, atom3);
}

#[test]
fn test_complex_syntax_kinds() {
    // Test various syntax kinds display correctly
    let kinds = vec![
        (SyntaxKind::BinOp, "binary operation"),
        (SyntaxKind::UnaryOp, "unary operation"),
        (SyntaxKind::MatchArm, "match arm"),
        (SyntaxKind::ConstructorPattern, "constructor pattern"),
        (SyntaxKind::TacticSeq, "tactic sequence"),
        (SyntaxKind::HashCommand, "hash command"),
    ];

    for (kind, expected) in kinds {
        check_syntax_kind_display(kind, expected);
    }
}

#[test]
fn test_edge_cases() {
    // Test with maximum values
    let large_pos = SourcePos {
        line: u32::MAX,
        column: u32::MAX,
        offset: usize::MAX,
    };

    let range = SourceRange {
        start: large_pos,
        end: large_pos,
    };

    let atom = Syntax::Atom(SyntaxAtom {
        range,
        value: "".into(), // Empty string
    });

    assert_eq!(atom.as_str(), "");
    assert_eq!(atom.range(), Some(&range));

    // Test deeply nested structure
    let mut current = Syntax::Missing;
    for i in 0..10 {
        current = Syntax::Node(Box::new(SyntaxNode {
            kind: SyntaxKind::LeftParen,
            range: SourceRange {
                start: SourcePos {
                    line: 1,
                    column: i,
                    offset: i as usize,
                },
                end: SourcePos {
                    line: 1,
                    column: i + 1,
                    offset: (i + 1) as usize,
                },
            },
            children: vec![current].into(),
        }));
    }

    // Should have 10 levels of nesting
    let mut depth = 0;
    let mut node = &current;
    while let Syntax::Node(n) = node {
        depth += 1;
        if n.children.is_empty() {
            break;
        }
        node = &n.children[0];
    }
    assert_eq!(depth, 10);
}
