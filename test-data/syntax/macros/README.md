# Lean 4 Macro System Test Files

This directory contains test files for the Lean 4 macro system implementation.

## Files

### basic_macros.lean
- Simple macro definitions
- Macros with parameters
- Macros with attributes and precedence
- Category-specific macros

### macro_rules.lean
- Pattern-based macro expansion
- Multiple expansion rules
- Extending existing syntax
- Custom tactics via macro_rules

### notation.lean
- Basic notation definitions
- Infix, prefix, postfix notations
- Precedence and associativity
- Unicode notation
- Scoped and local notation

### syntax_declarations.lean
- Syntax category declarations
- Syntax with parameters and repetitions
- Optional components and alternatives
- Complex syntax patterns

### syntax_quotations.lean
- Syntax quotations: `(...)
- Antiquotations: $x
- Pattern matching on syntax
- Category-specific quotations

### advanced_macros.lean
- Recursive macro expansion
- Hygiene and variable binding
- Error handling in macros
- Variadic and conditional macros

### elab_macros.lean
- Interaction between macros and elaborators
- Custom elaborators using macro expansion
- Syntax transformation
- Pattern matching in elaborators

## Testing Strategy

These files test:
1. **Parsing**: Can the parser correctly parse all macro-related syntax?
2. **Syntax tree construction**: Are the AST nodes properly constructed?
3. **Error handling**: Do invalid macro definitions produce appropriate errors?
4. **Edge cases**: Unicode, nested quotations, complex patterns

## Usage

To test the parser with these files:
```rust
let content = std::fs::read_to_string("test-data/syntax/macros/basic_macros.lean")?;
let mut parser = Parser::new(&content);
let module = parser.module()?;
```

## Notes

- These files contain syntactically valid Lean 4 macro definitions
- They are not meant to be executed, only parsed
- Some constructs may not be fully implemented in the parser yet
- The files progressively increase in complexity