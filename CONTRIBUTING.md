# Contributing to Lean-Claude

Thank you for your interest in contributing to Lean-Claude! This document provides guidelines and instructions for contributing.

## Code of Conduct

Please be respectful and constructive in all interactions. We aim to create a welcoming environment for all contributors.

## Getting Started

1. Fork the repository
2. Clone your fork: `git clone https://github.com/YOUR_USERNAME/lean-claude.git`
3. Add upstream remote: `git remote add upstream https://github.com/xiyuzhai/lean-claude.git`
4. Create a new branch: `git checkout -b feature/your-feature-name`

## Development Setup

```bash
# Install Rust nightly
rustup toolchain install nightly
rustup default nightly

# Clone with submodules
git clone --recursive https://github.com/xiyuzhai/lean-claude.git
cd lean-claude

# Build the project
cargo build

# Run tests
cargo test

# Run with example
cargo run --bin leanc-rs -- examples/hello.lean
```

## Code Style

We use rustfmt and clippy to maintain consistent code style:

```bash
# Format code
cargo fmt

# Run clippy
cargo clippy --all-features --all-targets -- -D warnings

# Run both before committing
cargo fmt && cargo clippy
```

## Testing

- Write tests for new functionality
- Ensure all tests pass before submitting PR
- Use `expect-test` for snapshot testing
- Add integration tests for parser changes

## Commit Messages

Follow conventional commits format:
- `feat:` New features
- `fix:` Bug fixes
- `docs:` Documentation changes
- `style:` Code style changes (formatting)
- `refactor:` Code refactoring
- `test:` Test additions or changes
- `chore:` Maintenance tasks
- `perf:` Performance improvements

Examples:
```
feat: Add support for pattern matching in parser
fix: Handle unicode identifiers correctly
docs: Update parser documentation
```

## Pull Request Process

1. Update documentation for any changed functionality
2. Add tests for new features
3. Ensure CI passes (tests, formatting, clippy)
4. Update CHANGELOG.md if applicable
5. Request review from maintainers

## Project Structure

```
lean-claude/
├── crates/
│   ├── abstractions/     # Core abstractions (eterned, idx-arena)
│   ├── syntax/          # Parser and syntax tree
│   ├── semantics/       # Type checking and elaboration
│   ├── mir/            # Intermediate representation
│   └── utils/          # Utilities and driver
├── apps/               # Binary applications
├── test-data/         # Test files and mathlib4
└── examples/          # Example Lean files
```

## Areas for Contribution

Current areas where help is particularly welcome:

1. **Parser Extensions**
   - Operator precedence parsing
   - Pattern matching syntax
   - Tactic mode support
   - Macro expansion

2. **Type System**
   - Implement elaborator
   - Universe level inference
   - Implicit argument resolution

3. **Testing**
   - Expand test coverage
   - Add mathlib4 integration tests
   - Performance benchmarks

4. **Documentation**
   - API documentation
   - Architecture guides
   - User tutorials

## Questions?

Feel free to:
- Open an issue for questions
- Join discussions in existing issues
- Reach out to maintainers

Thank you for contributing to Lean-Claude!