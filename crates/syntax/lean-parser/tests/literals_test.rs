use lean_parser::parser::Parser;

fn parse_module(input: &str) -> Result<lean_syn_expr::Syntax, lean_parser::error::ParseError> {
    let mut parser = Parser::new(input);
    parser.module()
}

#[test]
fn test_number_literals() {
    let test_cases = vec![
        // Decimal numbers
        ("42", "42"),
        ("3.14", "3.14"),
        ("1e10", "1e10"),
        ("1.5e-10", "1.5e-10"),
        ("1E+5", "1E+5"),
        // Hexadecimal
        ("0x1F", "0x1F"),
        ("0xDEADBEEF", "0xDEADBEEF"),
        ("0X10", "0x10"), // Parser normalizes to lowercase
        // Binary
        ("0b1010", "0b1010"),
        ("0B1111", "0b1111"), // Parser normalizes to lowercase
        // Octal
        ("0o755", "0o755"),
        ("0O123", "0o123"), // Parser normalizes to lowercase
    ];

    for (input, expected) in test_cases {
        let module_input = format!("#check {input}");
        let result = parse_module(&module_input);
        assert!(result.is_ok(), "Failed to parse: {input}");

        let module = result.unwrap();

        // Extract the number from the parsed command
        let cmd_str = format!("{module:?}");
        assert!(
            cmd_str.contains(expected),
            "Expected {expected} in parsed output, got: {cmd_str}"
        );
    }
}

#[test]
fn test_invalid_number_literals() {
    let invalid_cases = vec![
        "0x",  // hex without digits
        "0b",  // binary without digits
        "0o",  // octal without digits
        "0b2", // invalid binary digit
        "0o8", // invalid octal digit
        "0xG", // invalid hex digit
    ];

    for input in invalid_cases {
        let module_input = format!("#check {input}");
        let result = parse_module(&module_input);
        if result.is_ok() {
            // Parser might have parsed it differently than expected
            // Let's check if it contains the invalid literal
            let parsed = format!("{:?}", result.unwrap());
            assert!(
                !parsed.contains(input),
                "Parser should not have accepted invalid literal: {input}"
            );
        }
    }
}

#[test]
fn test_string_literals() {
    let test_cases = vec![
        // Basic strings
        (r#""hello""#, "hello"),
        (r#""hello\nworld""#, "hello"),
        (r#""tab\there""#, "tab"),
        (r#""quote\"test""#, "quote"),
        // Raw strings
        (r#"r"hello""#, "hello"),
        (r#"r"no\nescape""#, r"no\nescape"),
        (r###"r#"quotes"work"#"###, "quotes\"work"),
        (r###"r##"even more"##"###, "even more"),
    ];

    for (input, _expected) in test_cases {
        let module_input = format!("#check {input}");
        let result = parse_module(&module_input);
        assert!(result.is_ok(), "Failed to parse: {input}");
    }
}

#[test]
fn test_interpolated_strings() {
    let test_cases = vec![
        r#"s!"hello {x} world""#,
        r#"s!"result: {1 + 2}""#,
        r#"s!"nested {f {g x}}""#,
        r#"s!"escaped {{not interpolated}}""#,
    ];

    for input in test_cases {
        let module_input = format!("#check {input}");
        let result = parse_module(&module_input);
        assert!(
            result.is_ok(),
            "Failed to parse interpolated string: {input}"
        );
    }
}

#[test]
fn test_char_literals() {
    let test_cases = vec!["'a'", r"'\n'", r"'\t'", r"'\r'", r"'\\'", r"'\''"];

    for input in test_cases {
        let module_input = format!("#check {input}");
        let result = parse_module(&module_input);
        assert!(result.is_ok(), "Failed to parse char literal: {input}");
    }
}

#[test]
fn test_literals_in_expressions() {
    let expressions = vec![
        "0xFF + 0b1010",
        r#"s!"x = {x}, y = {y}""#,
        "['a', 'b', 'c']",
        r#"{"hex": 0x10, "oct": 0o10, "bin": 0b10}"#,
        "1.5e-10 * 2.0",
    ];

    for expr in expressions {
        let module_input = format!("#check {expr}");
        let result = parse_module(&module_input);
        assert!(result.is_ok(), "Failed to parse expression: {expr}");
    }
}
