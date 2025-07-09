# Development Guide

This guide covers the development workflow for the lean-claude project.

## Quick Start

```bash
# Run all checks before committing
make check

# Auto-fix formatting and clippy warnings
make fix

# Run tests
make test

# Build the project
make build
```

## Makefile Commands

The project includes a Makefile to streamline common development tasks.

### Main Commands

- `make` or `make all` - Run all checks (format, clippy, tests)
- `make check` - Run format check, clippy, and quick tests
- `make fix` - Auto-fix formatting and clippy warnings
- `make test` - Run all tests
- `make build` - Build the project
- `make clean` - Clean build artifacts

### Development Workflow

- `make fmt` - Format code
- `make fmt-check` - Check code formatting without modifying
- `make clippy` - Run clippy linter
- `make clippy-fix` - Run clippy and apply fixes
- `make test-quick` - Run quick tests (lib and bins only)
- `make dev-check` - Format, fix clippy warnings, and test

### Git Hooks

The project uses git hooks to ensure code quality. They are automatically installed when you clone the repo.

- `make pre-commit` - Run pre-commit checks (called by git hook)
- `make pre-push` - Run pre-push checks (called by git hook)
- `make install-hooks` - Reinstall git hooks if needed

#### Bypassing Hooks (Use with Caution!)

Sometimes you may need to bypass hooks for emergency fixes:

- `make commit-no-verify` - Commit without running checks
- `make push-no-verify` - Push without running checks
- Or use git directly: `git commit --no-verify`

### Other Useful Commands

- `make build-release` - Build optimized release version
- `make check-crate CRATE=name` - Check a specific crate
- `make update` - Update dependencies
- `make doc` - Generate documentation
- `make doc-open` - Generate and open documentation in browser
- `make ci` - Run full CI checks (format, clippy, all tests)
- `make help` - Show all available commands

## Development Tips

### Before Committing

Always run checks before committing:

```bash
make check
```

If there are issues, you can auto-fix most of them:

```bash
make fix
```

### Working on a Specific Crate

To check only a specific crate:

```bash
make check-crate CRATE=lean-parser
```

### Running Tests

For quick iteration during development:

```bash
make test-quick  # Fast tests only
```

For comprehensive testing:

```bash
make test  # All tests including ignored ones
```

### Dealing with Clippy Warnings

If clippy is complaining about test code:

1. Fix the warnings if they're valid
2. For test-specific issues, you can add `#[allow(clippy::lint_name)]` to the test
3. Run `make clippy-fix` to auto-fix what's possible

## Project Structure

The project is organized as a Cargo workspace with multiple crates:

- `crates/syntax/` - Parsing and syntax-related crates
  - `lean-parser` - Main parser implementation
  - `lean-syn-expr` - Syntax expression types
- `crates/semantics/` - Semantic analysis crates
  - `lean-kernel` - Core type system
  - `lean-elaborator` - Type elaboration
  - `lean-macro-expander` - Macro expansion
  - `lean-meta` - Metaprogramming support
- `crates/mir/` - Intermediate representation
  - `lean-ir` - IR types
  - `lean-codegen` - Code generation
- `crates/utils/` - Utility crates
- `crates/abstractions/` - Core abstractions like string interning

## Troubleshooting

### Pre-commit Hook Fails

If the pre-commit hook fails:

1. Run `make fix` to auto-fix issues
2. Review remaining issues with `make check`
3. Fix manually if needed
4. If you must bypass: `git commit --no-verify` (not recommended)

### Clippy Warnings in Tests

For test files, some clippy warnings might be overly strict. You can:

1. Fix the warning if it makes sense
2. Allow specific lints in test files
3. Focus on fixing warnings in library code first

### Build Issues

If you encounter build issues:

1. `make clean` - Clean all build artifacts
2. `cargo update` - Update dependencies
3. Check that you're using the correct Rust version (see rust-toolchain.toml)

## Contributing

1. Create a feature branch
2. Make your changes
3. Run `make check` to ensure quality
4. Commit with descriptive messages
5. Push and create a pull request

The CI will run the same checks as `make ci`, so running this locally helps catch issues early.