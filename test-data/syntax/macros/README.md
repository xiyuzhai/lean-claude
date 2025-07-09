# Lean 4 Macro Expansion Examples

This directory contains examples of Lean 4's macro system and how macros are expanded.

## Overview

Lean 4 macros are pure syntax transformations that happen during parsing. They allow you to extend the language with new syntax that gets transformed into core Lean expressions.

## Files in this Directory

- `basic_macros.lean` - Basic macro definitions
- `advanced_macros.lean` - Advanced macro features
- `macro_rules.lean` - Pattern-based macro rules
- `syntax_quotations.lean` - Syntax quotation examples
- `macro_expansion_examples.lean` - **Examples showing macro expansions**
- `expansion_traces.lean` - **Step-by-step expansion traces**
- `expansion_demo.rs` - Rust demo program for testing expansions

## Quick Examples

### 1. Simple Value Macro

```lean
macro "answer" : term => `(42)
def x := answer
-- Expands to: def x := 42
```

### 2. Parameter Substitution

```lean
macro "double" x:term : term => `($x + $x)
def y := double 21
-- Expands to: def y := 21 + 21
```

### 3. Nested Expansion

```lean
macro "twice" x:term : term => `($x + $x)
macro "quad" x:term : term => `(twice (twice $x))
def z := quad 5
-- Expands to: def z := ((5 + 5) + (5 + 5))
```

### 4. Control Flow Macros

```lean
macro "unless" c:term "do" body:term : term => `(if !$c then $body)
def result := unless false do 100
-- Expands to: def result := if !false then 100
```

## How Macro Expansion Works

1. **Parsing**: The parser encounters a macro invocation
2. **Pattern Matching**: The macro's pattern is matched against the syntax
3. **Binding**: Antiquotations (`$x`) are bound to matched syntax elements
4. **Template Substitution**: The template is instantiated with bindings
5. **Hygiene**: Fresh names are generated to avoid variable capture
6. **Recursive Expansion**: The result is expanded again if it contains more macros

## Testing Macro Expansion

To see macro expansion in action:

```bash
# Run the Rust demo
cd /path/to/lean-claude
cargo run --example macro_expansion_demo

# Or use the parser tests
cargo test -p lean-parser expansion_test
```

## Key Concepts

- **Syntax Quotations**: `` `(expr) `` - represents Lean syntax
- **Antiquotations**: `$x` - splices bound syntax into quotations
- **Categories**: `:term`, `:tactic`, etc. - specify syntax categories
- **Hygiene**: Automatic renaming prevents variable capture
- **Precedence**: `macro:50` - controls parsing precedence

## Advanced Features

- Pattern matching with `macro_rules`
- Multiple patterns for one macro
- Custom syntax categories
- Macro attributes (`@[simp]`, etc.)
- Recursive macro expansion
- Splicing lists with `$xs,*`