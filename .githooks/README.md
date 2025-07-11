# Git Hooks for lean-claude

This directory contains Git hooks to ensure code quality before commits and pushes.

## Setup

To install these hooks, run:

```bash
./scripts/setup-hooks.sh
```

Or manually copy the hooks:

```bash
cp .githooks/* .git/hooks/
chmod +x .git/hooks/*
```

## Available Hooks

### pre-commit
Runs before each commit to ensure:
- Code is properly formatted (`cargo fmt`)
- No clippy warnings (`cargo clippy`)
- All tests pass (`cargo test`)

### pre-push
Runs before pushing to remote to ensure:
- All pre-commit checks pass
- Project builds successfully
- Comprehensive test suite passes
- Warns about TODO/FIXME comments

## Bypassing Hooks

In emergency situations, you can bypass hooks using:

```bash
# Bypass pre-commit hook
git commit --no-verify -m "Emergency fix"

# Bypass pre-push hook
git push --no-verify
```

**⚠️ Warning**: Only bypass hooks when absolutely necessary. Always run the checks manually later:

```bash
cargo fmt --all
cargo clippy --all-features --workspace -- -D warnings
cargo test --all-features --workspace
```

## Customization

Feel free to modify these hooks to suit your workflow. Common customizations:
- Add specific test suites
- Check for security vulnerabilities with `cargo audit`
- Validate commit message format
- Check for large files

## Troubleshooting

If hooks aren't running:
1. Ensure they're executable: `chmod +x .git/hooks/*`
2. Check Git version: `git --version` (should be 2.9+)
3. Verify hook location: `ls -la .git/hooks/`

If tests fail in hooks but pass manually:
1. Ensure cargo environment is sourced
2. Check for environment-specific issues
3. Run with verbose output: `bash -x .git/hooks/pre-commit`