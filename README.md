# Lean-Claude

[![CI](https://github.com/xiyuzhai/lean-claude/actions/workflows/ci.yml/badge.svg)](https://github.com/xiyuzhai/lean-claude/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

A complete reimplementation of the Lean4 compiler in Rust, following Lean4's architecture and design decisions.

## Project Overview

This project aims to rewrite the entire Lean4 compiler toolchain in Rust while maintaining compatibility with existing Lean4 code and libraries like mathlib4. We follow Lean4's architectural decisions including its lexer-less parser, elaboration system, and code generation pipeline.

## Architecture Overview

The compiler follows Lean4's pipeline:
1. **Parsing**: Character stream → Syntax tree (no separate lexer)
2. **Elaboration**: Syntax → Expr with macro expansion and type inference
3. **Type Checking**: Validate expressions in the kernel
4. **IR Generation**: Expr → Intermediate Representation
5. **Code Generation**: IR → C code → Native binary

## Implementation Phases

### Phase 0: Project Setup
- [x] Create project structure
- [ ] Set up Cargo workspace with multiple crates
- [ ] Configure testing framework
- [ ] Set up CI/CD pipeline

### Phase 1: Lexer-less Parser
**Goal**: Implement a combinatoric, recursive-descent parser that directly consumes character streams

#### Core Components:
- [ ] Parser monad and combinator framework
- [ ] Input stream with position tracking and backtracking
- [ ] Memoization for packrat parsing
- [ ] Error recovery and reporting

#### Parser Categories:
- [ ] **Basic parsers**: whitespace, identifiers, literals
- [ ] **Command parsers**: definitions, imports, namespace management
- [ ] **Term parsers**: expressions, applications, lambda abstractions
- [ ] **Tactic parsers**: tactic sequences and combinators
- [ ] **Do-notation parsers**: monadic syntax support

#### Testing:
- [ ] Unit tests for each parser combinator
- [ ] Property-based testing with QuickCheck
- [ ] Parse test suite from Lean4 repository
- [ ] Roundtrip tests (parse → pretty-print → parse)

### Phase 2: Core Data Structures
**Goal**: Implement Lean's AST and core types

#### Syntax Tree:
- [ ] `Syntax` enum with all node types
- [ ] Source position information
- [ ] Pretty-printing infrastructure

#### Expression AST:
- [ ] `Expr` enum with constructors:
  - [ ] Variables: `bvar`, `fvar`, `mvar`
  - [ ] Types: `sort`, `const`
  - [ ] Terms: `app`, `lam`, `forallE`, `letE`
  - [ ] Literals and metadata: `lit`, `mdata`, `proj`
- [ ] `Level` for universe levels
- [ ] `Name` for hierarchical names
- [ ] `BinderInfo` for implicit/explicit arguments

#### Environment:
- [ ] Declaration storage
- [ ] Constant management
- [ ] Module system

#### Testing:
- [ ] Serialization/deserialization tests
- [ ] Memory layout optimization benchmarks
- [ ] Property tests for AST invariants

### Phase 3: Elaborator
**Goal**: Transform syntax trees into fully elaborated expressions

#### Core Features:
- [ ] Macro expansion system
- [ ] Syntax → Expr transformation
- [ ] Implicit argument inference
- [ ] Type class resolution
- [ ] Unification algorithm
- [ ] Local context management

#### Elaboration Strategies:
- [ ] Term elaboration
- [ ] Command elaboration
- [ ] Tactic elaboration
- [ ] Do-notation desugaring

#### Testing:
- [ ] Elaborate simple terms from mathlib4
- [ ] Test implicit argument resolution
- [ ] Verify type class instance selection
- [ ] Macro expansion tests

### Phase 4: Type Checker and Meta Operations
**Goal**: Implement the trusted kernel and metaprogramming infrastructure

#### Kernel:
- [ ] Type checking algorithm
- [ ] Definitional equality
- [ ] Reduction and normalization
- [ ] Inductive type support
- [ ] Universe constraint checking

#### Meta Framework:
- [ ] Meta-variable management
- [ ] Tactic state representation
- [ ] Goal management
- [ ] Proof term construction

#### Testing:
- [ ] Verify core type theory axioms
- [ ] Test against Lean4's kernel
- [ ] Proof checking for mathlib4 theorems
- [ ] Performance benchmarks

### Phase 5: IR and Code Generation
**Goal**: Compile elaborated terms to executable code

#### IR Design:
- [ ] Intermediate representation types
- [ ] Optimization passes
- [ ] Closure conversion
- [ ] Case compilation
- [ ] RC (reference counting) insertion

#### Code Generation:
- [ ] C code emission
- [ ] FFI support
- [ ] Runtime system interface
- [ ] Memory management

#### Testing:
- [ ] Compile and run Lean4 test suite
- [ ] Benchmark against Lean4 compiler
- [ ] Memory leak detection
- [ ] Performance profiling

### Phase 6: Integration and Advanced Features
**Goal**: Full compatibility with Lean4 ecosystem

#### Features:
- [ ] Lake build system integration
- [ ] Plugin system support
- [ ] Server mode for IDE support
- [ ] Incremental compilation
- [ ] Module system and imports

#### Compatibility Testing:
- [ ] Build and check mathlib4
- [ ] Run Lean4 test suite
- [ ] Performance comparison
- [ ] Memory usage analysis

## Development Guidelines

### Code Organization
```
lean-rs/
├── parser/          # Lexer-less parser implementation
├── syntax/          # Syntax tree definitions
├── kernel/          # Type checker and core
├── elaborator/      # Elaboration and macro expansion
├── meta/            # Metaprogramming framework
├── ir/              # Intermediate representation
├── codegen/         # C code generation
├── tests/           # Test suites
└── benches/         # Performance benchmarks
```

### Testing Strategy
1. **Unit tests**: Test individual components in isolation
2. **Integration tests**: Test component interactions
3. **Compatibility tests**: Compare output with Lean4
4. **Performance tests**: Ensure competitive performance
5. **Fuzzing**: Property-based testing for parsers and type checker

### Performance Goals
- Parser: < 2x slower than Lean4
- Type checker: Comparable to Lean4
- Code generation: Within 20% of Lean4
- Memory usage: Comparable or better

## Current Status

- [x] Phase 0: Project Setup
- [x] Phase 1: Lexer-less Parser (Basic implementation complete)
- [ ] Phase 2: Core Data Structures (In progress)
- [ ] Phase 3: Elaborator
- [ ] Phase 4: Type Checker
- [ ] Phase 5: Code Generation
- [ ] Phase 6: Integration

### Recent Progress
- ✅ Implemented lexer-less parser with all major commands
- ✅ Added support for terms, applications, and binders
- ✅ Created test framework with expect-test
- ✅ Set up CI/CD with GitHub Actions

## Contributing

This is a complex project requiring deep understanding of:
- Type theory and dependent types
- Compiler construction
- Rust systems programming
- Lean4 internals

## References

- [Lean4 Repository](https://github.com/leanprover/lean4)
- [Lean4 Documentation](https://leanprover.github.io/lean4/doc/)
- [mathlib4](https://github.com/leanprover-community/mathlib4)