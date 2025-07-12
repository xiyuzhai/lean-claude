#!/usr/bin/env python3

import re
import sys

def fix_test_file(file_path):
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Pattern 1: Fix SyntaxAtom struct construction
    pattern1 = r'SyntaxAtom\s*\{\s*range:\s*([^,]+),\s*value:\s*([^}]+)\s*\}'
    replacement1 = r'SyntaxAtom::new(\1, \2)'
    
    # Pattern 2: Fix SyntaxNode struct construction (simplified cases)
    pattern2 = r'SyntaxNode\s*\{\s*kind:\s*([^,]+),\s*range:\s*([^,]+),\s*children:\s*([^}]+)\s*\}'
    replacement2 = r'SyntaxNode::new(\1, \2, \3)'
    
    original_content = content
    content = re.sub(pattern1, replacement1, content)
    content = re.sub(pattern2, replacement2, content)
    
    if content != original_content:
        with open(file_path, 'w') as f:
            f.write(content)
        print(f"Fixed: {file_path}")
        return True
    return False

if __name__ == "__main__":
    file_path = sys.argv[1] if len(sys.argv) > 1 else "/home/ubuntu/lean-claude/crates/syntax/lean-syn-expr/src/tests.rs"
    fixed = fix_test_file(file_path)
    if fixed:
        print("File updated successfully")
    else:
        print("No changes needed")