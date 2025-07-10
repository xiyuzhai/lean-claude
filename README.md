# Lean-Claude

[![CI](https://github.com/xiyuzhai/lean-claude/actions/workflows/ci.yml/badge.svg)](https://github.com/xiyuzhai/lean-claude/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

A complete reimplementation of the Lean4 compiler in Rust, following Lean4's architecture and design decisions.

## Project Overview

This project aims to rewrite the entire Lean4 compiler toolchain in Rust while maintaining compatibility with existing Lean4 code and libraries like mathlib4. We follow Lean4's architectural decisions including its lexer-less parser, elaboration system, and code generation pipeline.

## Quick Start

```bash
# Clone the repository
git clone https://github.com/xiyuzhai/lean-claude.git
cd lean-claude

# Run all checks
make check

# Build the project
make build

# Run tests
make test

# See all available commands
make help
```

For detailed development instructions, see [DEVELOPMENT.md](DEVELOPMENT.md).

## Current Status

### ✅ Completed
- **Project Setup**: Workspace structure, CI/CD, development tooling
- **Basic Parser**: Lexer-less parser with core functionality
  - All major command parsers (def, theorem, class, structure, inductive, etc.)
  - Term parsers (lambda, forall, let, have, show, match, if-then-else)
  - Operator precedence parsing with Pratt parser
  - Pattern matching syntax
  - Unicode support
  - Comment handling
- **Macro System**: Basic macro expansion infrastructure
  - Simple `macro` definitions with parameters
  - Syntax quotations `` `(...) `` and antiquotations `$x`
  - Pattern matching and template substitution
  - Hygienic name generation
  - Recursive macro expansion
- **Core Data Structures**: Foundation types
  - `Syntax` tree with source positions
  - `Expr` AST (bvar, fvar, app, lambda, forall, let, literals)
  - `Level` for universe levels
  - `Name` for hierarchical names
  - String interning with `eterned`

### 🚧 In Progress
- **Parser Enhancements**
  - [ ] `macro_rules` with multiple patterns
  - [ ] Built-in macros (panic!, assert!, etc.)
  - [ ] Macro splices `$xs,*`
  - [ ] Full tactic mode parsing
  - [ ] Attribute parsing
  - [ ] Notation and custom operators
- **Testing Infrastructure**
  - [ ] mathlib4 parsing tests
  - [ ] Performance benchmarks
  - [ ] Fuzzing framework

### 📋 Next Steps

1. **Complete Macro System** (High Priority)
   - Implement `macro_rules` for pattern-based macros
   - Add built-in macros (panic!, assert!, unreachable!)
   - Support macro splices for list handling
   - Custom syntax categories

2. **Parser Robustness**
   - Error recovery mechanisms
   - Better error messages with suggestions
   - Incremental parsing support
   - Performance optimization

3. **Begin Elaboration Phase**
   - Type inference infrastructure
   - Implicit argument resolution
   - Type class instance search
   - Metavariable management

## Architecture

```
lean-claude/
├── crates/
│   ├── abstractions/
│   │   └── eterned/          # String interning
│   ├── syntax/
│   │   ├── lean-parser/      # Lexer-less parser
│   │   └── lean-syn-expr/    # Syntax tree types
│   ├── semantics/
│   │   ├── lean-kernel/      # Core types (Expr, Level, Name)
│   │   ├── lean-macro-expander/ # Macro expansion
│   │   ├── lean-elaborator/  # Type elaboration (WIP)
│   │   └── lean-meta/        # Metaprogramming (WIP)
│   └── mir/
│       ├── lean-ir/          # Intermediate representation
│       └── lean-codegen/     # Code generation
├── test-data/                # Test files and examples
└── Makefile                  # Development commands
```

## Development Roadmap

### Phase 1: Parser & Macros ✅ (90% Complete)
- [x] Lexer-less parser architecture
- [x] Command and term parsing
- [x] Basic macro expansion
- [ ] Complete macro system
- [ ] Full Lean4 syntax support

### Phase 2: Elaboration 🚧 (Starting Soon)
- [ ] Syntax to Expr transformation
- [ ] Type inference algorithm
- [ ] Implicit argument synthesis
- [ ] Type class resolution
- [ ] Unification

### Phase 3: Type Checking 📅
- [ ] Kernel implementation
- [ ] Definitional equality
- [ ] Inductive types
- [ ] Universe constraints
- [ ] Proof checking

### Phase 4: Code Generation 📅
- [ ] IR design
- [ ] Optimization passes
- [ ] C code emission
- [ ] Runtime integration

### Phase 5: Ecosystem Integration 📅
- [ ] Lake build system
- [ ] LSP server
- [ ] mathlib4 compatibility
- [ ] Performance optimization

## Key Features

- **Lexer-less Parser**: Direct character stream parsing without tokenization
- **Hygienic Macros**: Macro system with automatic name generation to prevent capture
- **String Interning**: Efficient string handling with SHA512-based interning
- **Comprehensive Testing**: expect-test, property-based testing, and real-world test cases
- **Development Tooling**: Makefile, pre-commit hooks, and CI/CD integration

## Contributing

See [DEVELOPMENT.md](DEVELOPMENT.md) for development guidelines. Key requirements:
- Understanding of type theory and compilers
- Rust systems programming experience
- Familiarity with Lean4 helpful but not required

## Performance Goals

- Parser: **Faster than Lean4** (target: 1.2-2x faster)
- Type checker: **Comparable to Lean4** (target: within 10% either direction)
- Code generation: **Within 10% of Lean4** (target: comparable or faster)
- Memory usage: **Better than Lean4** (target: 20-30% lower peak usage)

## References

- [Lean4 Repository](https://github.com/leanprover/lean4)
- [Lean4 Documentation](https://leanprover.github.io/lean4/doc/)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [The Lean 4 Theorem Prover and Programming Language](https://leanprover.github.io/papers/lean4.pdf)

## License

This project is dual-licensed under MIT and Apache 2.0 licenses.