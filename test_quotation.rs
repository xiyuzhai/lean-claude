use lean_parser::Parser;

fn main() {
    let input = "`($n + 1)";
    let mut parser = Parser::new(input);
    let result = parser.term();
    println\!("Quotation result: {:?}", result);
}
EOF < /dev/null
