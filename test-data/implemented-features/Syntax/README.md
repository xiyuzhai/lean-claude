# Lean 4 Syntax Test Suite

This directory contains comprehensive test cases for the Lean 4 parser implementation.

## Directory Structure

- `basic/` - Basic lexical elements (identifiers, literals, comments)
- `expressions/` - Expression syntax (lambda, application, let/have, match, operators)
- `types/` - Type syntax (basic types, forall/Pi types)
- `commands/` - Command syntax (def, theorem, structure, inductive, instance)
- `tactics/` - Tactic syntax (basic tactics, structured proofs)
- `patterns/` - Pattern matching syntax
- `unicode/` - Unicode symbol support
- `errors/` - Parse error test cases

## Test Categories

### Basic Syntax
- **identifiers.lean** - All forms of identifiers including unicode
- **literals.lean** - Numbers, strings, characters with various formats
- **comments.lean** - Single-line, block, nested, and doc comments

### Expressions
- **lambda.lean** - Lambda expressions with various parameter styles
- **application.lean** - Function application, explicit args, named args
- **let_have.lean** - Let bindings and have statements
- **match.lean** - Pattern matching expressions
- **operators.lean** - All operator types and precedences

### Types
- **basic.lean** - Basic types, universes, type constructors
- **forall.lean** - Forall/Pi types with various binders

### Commands
- **definitions.lean** - def, abbrev, partial, protected, etc.
- **theorems.lean** - theorem, lemma, example with various proof styles
- **structures.lean** - structure and class definitions
- **inductives.lean** - Inductive types and families
- **instances.lean** - Type class instances

### Tactics
- **basic.lean** - Common tactics (rfl, simp, apply, etc.)
- **structured.lean** - Structured proofs (calc, have, suffices)

### Patterns
- **basic.lean** - Simple pattern matching
- **advanced.lean** - Dependent patterns, absurd patterns, etc.

### Unicode
- **symbols.lean** - Comprehensive unicode symbol coverage

### Errors
- **parse_errors.lean** - Various parsing error scenarios

## Running Tests

These test files are designed to be parsed by the lean-parser implementation
to verify correct handling of Lean 4 syntax. Each file focuses on specific
syntax features to enable targeted testing and debugging.

## Adding New Tests

When adding new test cases:
1. Place them in the appropriate category directory
2. Use descriptive names for test definitions
3. Include comments explaining what is being tested
4. Cover both typical usage and edge cases