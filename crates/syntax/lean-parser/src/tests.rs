use crate::parser::Parser;
use expect_test::{expect, Expect};

mod module_tests;

fn check_parse(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    match parser.identifier() {
        Ok(syntax) => expected.assert_eq(&format!("{:?}", syntax)),
        Err(e) => expected.assert_eq(&format!("Error: {}", e)),
    }
}

#[test]
fn test_identifier() {
    check_parse(
        "hello",
        expect![[r#"Atom(SyntaxAtom { range: SourceRange { start: SourcePos { line: 1, column: 1, offset: 0 }, end: SourcePos { line: 1, column: 6, offset: 5 } }, value: BaseCoword { data: "hello" } })"#]],
    );
    
    check_parse(
        "hello_world",
        expect![[r#"Atom(SyntaxAtom { range: SourceRange { start: SourcePos { line: 1, column: 1, offset: 0 }, end: SourcePos { line: 1, column: 12, offset: 11 } }, value: BaseCoword { data: "hello_world" } })"#]],
    );
    
    check_parse(
        "x'",
        expect![[r#"Atom(SyntaxAtom { range: SourceRange { start: SourcePos { line: 1, column: 1, offset: 0 }, end: SourcePos { line: 1, column: 3, offset: 2 } }, value: BaseCoword { data: "x'" } })"#]],
    );
}

#[test]
fn test_number() {
    let mut parser = Parser::new("42");
    let result = parser.number();
    expect![[r#"Ok(Atom(SyntaxAtom { range: SourceRange { start: SourcePos { line: 1, column: 1, offset: 0 }, end: SourcePos { line: 1, column: 3, offset: 2 } }, value: BaseCoword { data: "42" } }))"#]]
        .assert_eq(&format!("{:?}", result));
    
    let mut parser = Parser::new("3.14");
    let result = parser.number();
    expect![[r#"Ok(Atom(SyntaxAtom { range: SourceRange { start: SourcePos { line: 1, column: 1, offset: 0 }, end: SourcePos { line: 1, column: 5, offset: 4 } }, value: BaseCoword { data: "3.14" } }))"#]]
        .assert_eq(&format!("{:?}", result));
}

#[test]
fn test_string_literal() {
    let mut parser = Parser::new(r#""hello world""#);
    let result = parser.string_literal();
    expect![[r#"Ok(Atom(SyntaxAtom { range: SourceRange { start: SourcePos { line: 1, column: 1, offset: 0 }, end: SourcePos { line: 1, column: 14, offset: 13 } }, value: BaseCoword { data: "hello world" } }))"#]]
        .assert_eq(&format!("{:?}", result));
    
    let mut parser = Parser::new(r#""hello\nworld""#);
    let result = parser.string_literal();
    expect![[r#"Ok(Atom(SyntaxAtom { range: SourceRange { start: SourcePos { line: 1, column: 1, offset: 0 }, end: SourcePos { line: 1, column: 15, offset: 14 } }, value: BaseCoword { data: "hello\nworld" } }))"#]]
        .assert_eq(&format!("{:?}", result));
}

#[test]
fn test_keyword() {
    let mut parser = Parser::new("def");
    let result = parser.keyword("def");
    assert!(result.is_ok());
    
    let mut parser = Parser::new("define");
    let result = parser.keyword("def");
    assert!(result.is_err());
}

#[test]
fn test_whitespace_handling() {
    let mut parser = Parser::new("  \n  hello");
    parser.skip_whitespace();
    let result = parser.identifier();
    assert!(result.is_ok());
}

#[test]
fn test_comments() {
    let mut parser = Parser::new("-- this is a comment\nhello");
    parser.skip_whitespace_and_comments();
    let result = parser.identifier();
    assert!(result.is_ok());
    
    let mut parser = Parser::new("/- block comment -/ hello");
    parser.skip_whitespace_and_comments();
    let result = parser.identifier();
    assert!(result.is_ok());
    
    let mut parser = Parser::new("/- nested /- comment -/ -/ hello");
    parser.skip_whitespace_and_comments();
    let result = parser.identifier();
    assert!(result.is_ok());
}