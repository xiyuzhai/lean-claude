use crate::Parser;
use expect_test::{expect, Expect};

fn check_parse_positions(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let mut positions = Vec::new();
    
    while let Some(ch) = parser.peek() {
        let pos = parser.position();
        positions.push(format!(
            "char '{}' at line:{} col:{} offset:{}",
            ch, pos.line, pos.column, pos.offset
        ));
        parser.advance();
    }
    
    let output = positions.join("\n");
    expected.assert_eq(&output);
}

#[test]
fn test_unicode_positions() {
    check_parse_positions(
        "α → β",
        expect![[r#"
            char 'α' at line:1 col:1 offset:0
            char ' ' at line:1 col:2 offset:2
            char '→' at line:1 col:3 offset:3
            char ' ' at line:1 col:4 offset:6
            char 'β' at line:1 col:5 offset:7"#]],
    );
}

#[test]
fn test_ascii_positions() {
    check_parse_positions(
        "a -> b",
        expect![[r#"
            char 'a' at line:1 col:1 offset:0
            char ' ' at line:1 col:2 offset:1
            char '-' at line:1 col:3 offset:2
            char '>' at line:1 col:4 offset:3
            char ' ' at line:1 col:5 offset:4
            char 'b' at line:1 col:6 offset:5"#]],
    );
}

#[test]
fn test_mixed_unicode() {
    check_parse_positions(
        "∀α∈β",
        expect![[r#"
            char '∀' at line:1 col:1 offset:0
            char 'α' at line:1 col:2 offset:3
            char '∈' at line:1 col:3 offset:5
            char 'β' at line:1 col:4 offset:8"#]],
    );
}