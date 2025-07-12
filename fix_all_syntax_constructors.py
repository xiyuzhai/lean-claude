#!/usr/bin/env python3

import os
import re
import glob

def fix_syntax_constructors_file(file_path):
    """Fix all SyntaxNode and SyntaxAtom struct constructions to use constructors"""
    try:
        with open(file_path, 'r') as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return False
    
    original_content = content
    changed = False
    
    # Pattern 1: Fix simple SyntaxAtom struct construction
    pattern1 = r'SyntaxAtom\s*\{\s*range:\s*([^,]+),\s*value:\s*([^}]+)\s*\}'
    replacement1 = r'SyntaxAtom::new(\1, \2)'
    content = re.sub(pattern1, replacement1, content)
    
    # Pattern 2: Fix lean_syn_expr::SyntaxAtom struct construction
    pattern2 = r'lean_syn_expr::SyntaxAtom\s*\{\s*range:\s*([^,]+),\s*value:\s*([^}]+)\s*\}'
    replacement2 = r'lean_syn_expr::SyntaxAtom::new(\1, \2)'
    content = re.sub(pattern2, replacement2, content)
    
    # Pattern 3: Fix simple SyntaxNode struct construction
    # This regex handles multi-line patterns more robustly
    def replace_syntax_node(match):
        kind = match.group(1).strip()
        range_val = match.group(2).strip()
        children = match.group(3).strip()
        return f'SyntaxNode::new({kind}, {range_val}, {children})'
    
    pattern3 = r'SyntaxNode\s*\{\s*kind:\s*([^,]+?),\s*range:\s*([^,]+?),\s*children:\s*(.+?)\s*\}'
    content = re.sub(pattern3, replace_syntax_node, content, flags=re.MULTILINE | re.DOTALL)
    
    # Pattern 4: Fix lean_syn_expr::SyntaxNode struct construction
    def replace_lean_syntax_node(match):
        kind = match.group(1).strip()
        range_val = match.group(2).strip()
        children = match.group(3).strip()
        return f'lean_syn_expr::SyntaxNode::new({kind}, {range_val}, {children})'
    
    pattern4 = r'lean_syn_expr::SyntaxNode\s*\{\s*kind:\s*([^,]+?),\s*range:\s*([^,]+?),\s*children:\s*(.+?)\s*\}'
    content = re.sub(pattern4, replace_lean_syntax_node, content, flags=re.MULTILINE | re.DOTALL)
    
    # Pattern 5: Handle Box::new(SyntaxNode { ... }) patterns line by line
    lines = content.split('\n')
    result_lines = []
    i = 0
    
    while i < len(lines):
        line = lines[i]
        if 'Box::new(SyntaxNode {' in line or 'Box::new(lean_syn_expr::SyntaxNode {' in line:
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
                    if 'lean_syn_expr::SyntaxNode' in line:
                        new_line = f"{prefix}Box::new(lean_syn_expr::SyntaxNode::new({kind}, {range_val}, {children}))"
                    else:
                        new_line = f"{prefix}Box::new(SyntaxNode::new({kind}, {range_val}, {children}))"
                    
                    # Handle different contexts
                    if line.strip().startswith('Ok('):
                        result_lines.append(f"{prefix}Ok(Syntax::Node({new_line}))")
                    elif '=' in line:
                        var_part = line.split('=')[0].strip()
                        result_lines.append(f"{prefix}{var_part} = Syntax::Node({new_line});")
                    else:
                        result_lines.append(new_line)
                    
                    changed = True
                    i = j
                    continue
        
        result_lines.append(line)
        i += 1
    
    if changed:
        content = '\n'.join(result_lines)
    
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
        if fix_syntax_constructors_file(file_path):
            fixed_count += 1
    
    print(f"Processed {len(files)} files, fixed {fixed_count} files")

if __name__ == "__main__":
    main()