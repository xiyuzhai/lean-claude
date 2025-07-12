#!/bin/bash
# Test runner for Vim Lean Analyzer plugin

set -e

echo "Running Vim plugin tests..."

# Check if vim is available
if ! command -v vim &> /dev/null; then
    echo "ERROR: vim is not installed or not in PATH"
    exit 1
fi

# Check if vim has required features
if ! vim --version | grep -q "+job"; then
    echo "ERROR: vim does not have +job support required for the plugin"
    exit 1
fi

if ! vim --version | grep -q "+channel"; then
    echo "ERROR: vim does not have +channel support required for the plugin" 
    exit 1
fi

echo "✓ vim with required features found"

# Get the directory containing this script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
PLUGIN_DIR="$(dirname "$SCRIPT_DIR")"

echo "Testing plugin at: $PLUGIN_DIR"

# Test 1: Basic plugin functionality
echo ""
echo "=== Test 1: Plugin functionality ==="
cd "$PLUGIN_DIR"
if vim -u NONE -S test/test_runner.vim; then
    echo "✓ Plugin functionality tests passed"
else
    echo "✗ Plugin functionality tests failed"
    exit 1
fi

# Test 2: Syntax highlighting
echo ""
echo "=== Test 2: Syntax highlighting ==="
if vim -u NONE -S test/test_syntax.vim; then
    echo "✓ Syntax highlighting tests passed"
else
    echo "✗ Syntax highlighting tests failed"
    exit 1
fi

# Test 3: File type detection
echo ""
echo "=== Test 3: File type detection ==="
TEST_FILE=$(mktemp --suffix=.lean)
echo "def test : Nat := 42" > "$TEST_FILE"

if vim -u NONE -c "set runtimepath+=$PLUGIN_DIR" -c "filetype plugin on" -c "edit $TEST_FILE" -c "if &filetype == 'lean' | echo 'SUCCESS' | qall! | else | echo 'FAILED' | cquit! | endif"; then
    echo "✓ File type detection works"
else
    echo "✗ File type detection failed"
    rm -f "$TEST_FILE"
    exit 1
fi

rm -f "$TEST_FILE"

# Test 4: Indentation
echo ""
echo "=== Test 4: Indentation ==="
TEST_FILE=$(mktemp --suffix=.lean)
cat > "$TEST_FILE" << 'EOF'
def test : Nat :=
match x with
| 0 => 1
| n + 1 => n
EOF

if vim -u NONE -c "set runtimepath+=$PLUGIN_DIR" -c "filetype plugin indent on" -c "edit $TEST_FILE" -c "normal gg=G" -c "wq"; then
    echo "✓ Indentation works"
else
    echo "✗ Indentation failed"
    rm -f "$TEST_FILE"
    exit 1
fi

rm -f "$TEST_FILE"

echo ""
echo "=== All tests passed! ==="
echo "Vim plugin is working correctly."