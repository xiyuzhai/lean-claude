#!/usr/bin/env python3

import os
import re
import glob

def fix_boxed_syntax_file(file_path):
    """Fix syntax like Box::new(SyntaxNode { ... }) to use SyntaxNode::new()"""
    try:
        with open(file_path, 'r') as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return False
    
    original_content = content
    
    # Fix Box::new(SyntaxNode { ... }) patterns using a more aggressive approach
    # Split into lines and process 
    lines = content.split('\n')
    result_lines = []
    i = 0
    changed = False
    
    while i < len(lines):
        line = lines[i]
        if 'Box::new(SyntaxNode {' in line:
            # Find the complete structure
            indent = len(line) - len(line.lstrip())
            start_line = i
            brace_count = 1
            j = i + 1
            
            # Find the matching closing brace
            while j < len(lines) and brace_count > 0:
                if '{' in lines[j]:
                    brace_count += lines[j].count('{')
                if '}' in lines[j]:
                    brace_count -= lines[j].count('}')
                j += 1
            
            if brace_count == 0:
                # Extract the fields
                struct_lines = lines[start_line:j]
                struct_text = '\n'.join(struct_lines)
                
                # Extract kind, range, and children
                kind_match = re.search(r'kind:\s*([^,]+)', struct_text)
                range_match = re.search(r'range:\s*([^,]+)', struct_text)
                children_match = re.search(r'children:\s*(.+?)(?=\s*\})', struct_text, re.DOTALL)
                
                if kind_match and range_match and children_match:
                    kind = kind_match.group(1).strip()
                    range_val = range_match.group(1).strip()
                    children = children_match.group(1).strip()
                    
                    # Replace with SyntaxNode::new call
                    prefix = ' ' * indent
                    new_line = f"{prefix}Ok(Syntax::Node(Box::new(SyntaxNode::new({kind}, {range_val}, {children}))))"
                    if line.strip().startswith('Ok('):
                        result_lines.append(new_line)
                    else:
                        # Handle other cases
                        new_line = f"{prefix}Box::new(SyntaxNode::new({kind}, {range_val}, {children}))"
                        result_lines.append(new_line)
                    changed = True
                    i = j
                    continue
        
        result_lines.append(line)
        i += 1
    
    if changed:
        content = '\n'.join(result_lines)
    
    # Also fix lean_syn_expr::SyntaxNode { ... } patterns
    pattern2 = r'lean_syn_expr::SyntaxNode\s*\{\s*kind:\s*([^,]+?),\s*range:\s*([^,]+?),\s*children:\s*(.+?)\s*\}'
    replacement2 = r'lean_syn_expr::SyntaxNode::new(\1, \2, \3)'
    content = re.sub(pattern2, replacement2, content, flags=re.MULTILINE | re.DOTALL)
    
    if content != original_content:
        try:
            with open(file_path, 'w') as f:
                f.write(content)
            print(f"Fixed: {file_path}")
            return True
        except Exception as e:
            print(f"Error writing {file_path}: {e}")
            return False
    return False

def main():
    # Find all Rust files in the crates directory
    pattern = "/home/ubuntu/lean-claude/crates/**/*.rs"
    files = glob.glob(pattern, recursive=True)
    
    fixed_count = 0
    for file_path in files:
        if fix_boxed_syntax_file(file_path):
            fixed_count += 1
    
    print(f"Processed {len(files)} files, fixed {fixed_count} files")

if __name__ == "__main__":
    main()