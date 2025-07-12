#!/usr/bin/env python3
import os
import re

def fix_syntax_constructors(file_path):
    """Fix SyntaxNode and SyntaxAtom constructor calls in a file"""
    try:
        with open(file_path, 'r') as f:
            content = f.read()
        
        original_content = content
        
        # Pattern 1: Fix SyntaxNode struct construction
        # Match: SyntaxNode { kind: ..., range: ..., children: ... }
        pattern1 = r'SyntaxNode\s*\{\s*kind:\s*([^,]+),\s*range:\s*([^,]+),\s*children:\s*([^}]+)\s*\}'
        replacement1 = r'SyntaxNode::new(\1, \2, \3)'
        content = re.sub(pattern1, replacement1, content, flags=re.MULTILINE | re.DOTALL)
        
        # Pattern 2: Fix SyntaxAtom struct construction
        # Match: SyntaxAtom { range: ..., value: ... }
        pattern2 = r'SyntaxAtom\s*\{\s*range:\s*([^,]+),\s*value:\s*([^}]+)\s*\}'
        replacement2 = r'SyntaxAtom::new(\1, \2)'
        content = re.sub(pattern2, replacement2, content, flags=re.MULTILINE | re.DOTALL)
        
        if content != original_content:
            with open(file_path, 'w') as f:
                f.write(content)
            print(f"Fixed: {file_path}")
            return True
        return False
        
    except Exception as e:
        print(f"Error processing {file_path}: {e}")
        return False

def main():
    """Fix all Rust files in the codebase"""
    fixed_count = 0
    total_count = 0
    
    for root, dirs, files in os.walk("crates"):
        for file in files:
            if file.endswith(".rs"):
                file_path = os.path.join(root, file)
                total_count += 1
                if fix_syntax_constructors(file_path):
                    fixed_count += 1
    
    print(f"Processed {total_count} files, fixed {fixed_count} files")

if __name__ == "__main__":
    main()