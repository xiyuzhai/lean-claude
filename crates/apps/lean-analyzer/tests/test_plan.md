# Lean Analyzer Comprehensive Test Plan

## Overview
This document outlines exhaustive testing for lean-analyzer, focusing on superior error messages, quick fixes, and formatting support to address common complaints about Lean's misleading syntax errors.

## Test Categories

### 1. Beginner Syntax Error Tests
- **Missing imports**: `Nat` not found → suggest `#import Std.Init.Data.Nat`
- **Incorrect syntax**: `def f x := x` → suggest `def f (x : α) : α := x`
- **Missing type annotations**: `def f x := x + 1` → suggest explicit types
- **Parentheses errors**: `def f x : Nat := x + 1` → suggest `def f (x : Nat) : Nat := x + 1`
- **Indentation issues**: Mixed tabs/spaces → suggest consistent formatting
- **Missing colons**: `def f (x Nat) := x` → suggest `def f (x : Nat) := x`

### 2. Import and Namespace Errors
- **Module not found**: `import NonExistent` → suggest similar modules
- **Wrong import path**: `import Std.Data.List` → suggest correct `import Std.Data.List.Basic`
- **Namespace conflicts**: `open List` conflicts → suggest qualified names
- **Missing namespace**: `List.map` not found → suggest `import Std.Data.List.Basic`
- **Circular imports**: Detect and suggest restructuring
- **Case sensitivity**: `import std.data.list` → suggest `import Std.Data.List`

### 3. Type System Error Tests
- **Type mismatches**: Detailed explanations with suggestions
- **Implicit argument issues**: `@List.map` missing arguments → suggest explicit args
- **Universe level errors**: Clear explanations of Type/Sort issues
- **Coercion failures**: Suggest explicit conversions
- **Instance resolution**: Missing typeclass instances with suggestions

### 4. Quick Fixes and Code Actions
- **Auto-import**: Add missing imports automatically
- **Type annotations**: Insert inferred types
- **Refactoring**: Extract functions, rename symbols
- **Code organization**: Move definitions, split files
- **Documentation**: Add docstrings automatically

### 5. Formatting Support
- **Indentation**: Consistent 2-space indentation
- **Line length**: 100-character limit with smart wrapping
- **Alignment**: Function arguments, match cases
- **Spacing**: Around operators, after colons
- **Comments**: Proper spacing and alignment

### 6. LSP Integration Tests
- **Hover**: Type information, documentation
- **Go-to-definition**: Across files and modules
- **Find references**: All usages including implicit
- **Completion**: Context-aware suggestions
- **Diagnostics**: Real-time error reporting

### 7. Performance Tests
- **Large files**: 10k+ lines handling
- **Multiple projects**: Workspace scalability
- **Memory usage**: Efficient caching
- **Response time**: Sub-100ms for basic operations

## Error Message Quality Standards

### Before (Typical Lean Error):
```
type mismatch at term 'x'
  x : Nat
has type
  Nat
but is expected to have type
  String
```

### After (lean-analyzer Error):
```
Type mismatch: expected 'String', got 'Nat'

The expression 'x' has type 'Nat', but the context requires type 'String'.

Suggestions:
• Convert to string: x.toString
• Use string interpolation: s"{x}"
• Check if you meant to use a different variable

Help: https://lean-lang.org/theorem_proving_in_lean4/types.html
```

## Test Structure
- Unit tests for each error type
- Integration tests for LSP functionality
- Property-based tests for formatter
- Benchmark tests for performance
- Real-world scenario tests

## Success Criteria
- 95%+ accuracy in error suggestions
- Sub-100ms response time for diagnostics
- 100% test coverage for error handling
- Zero false positives in quick fixes
- Rust-analyzer quality user experience