#!/bin/bash
# Script to set up Git hooks for the project

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$( cd "$SCRIPT_DIR/.." && pwd )"

echo "Setting up Git hooks for lean-claude project..."

# Create hooks directory if it doesn't exist
mkdir -p "$PROJECT_ROOT/.git/hooks"

# Copy or link hooks
if [ -d "$PROJECT_ROOT/.githooks" ]; then
    echo "Copying hooks from .githooks directory..."
    cp -r "$PROJECT_ROOT/.githooks/"* "$PROJECT_ROOT/.git/hooks/"
    chmod +x "$PROJECT_ROOT/.git/hooks/"*
else
    echo "Hooks are already in place in .git/hooks/"
fi

# Make sure hooks are executable
chmod +x "$PROJECT_ROOT/.git/hooks/pre-commit" 2>/dev/null || true
chmod +x "$PROJECT_ROOT/.git/hooks/pre-push" 2>/dev/null || true

echo "✅ Git hooks have been set up successfully!"
echo ""
echo "The following hooks are now active:"
echo "  - pre-commit: Runs formatting, clippy, and tests before each commit"
echo "  - pre-push: Runs comprehensive checks before pushing to remote"
echo ""
echo "To bypass hooks in an emergency, use:"
echo "  - git commit --no-verify"
echo "  - git push --no-verify"
echo ""
echo "⚠️  Use --no-verify sparingly and only when absolutely necessary!"