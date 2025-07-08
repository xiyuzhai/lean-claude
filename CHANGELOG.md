# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- Complete lexer-less parser implementation
- Support for all major Lean4 commands (def, theorem, class, structure, inductive)
- Hash commands (#check, #eval, #print, #reduce)
- Term parsing (lambda, forall, let, have, show, applications)
- String interning system with eterned
- Basic test suite with expect-test
- CI/CD pipeline with GitHub Actions
- Dual licensing (MIT/Apache 2.0)

### Changed
- Reorganized crate structure for better modularity
- Improved parser error handling

### Fixed
- Circular dependencies in parser modules
- Module organization issues

## [0.0.1] - TBD

Initial development release.