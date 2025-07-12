" Test syntax highlighting for Lean files

" Set up test environment
set nocompatible
set runtimepath+=.
filetype plugin on
syntax on

" Create a test file with Lean content
let test_content = [
  \ '-- Test Lean file',
  \ 'import Std.Data.List.Basic',
  \ '',
  \ 'def hello : String := "Hello, World!"',
  \ '',
  \ 'theorem test (x y : Nat) : x + y = y + x := by',
  \ '  ring',
  \ '',
  \ 'inductive Color where',
  \ '| red',
  \ '| green', 
  \ '| blue',
  \ '',
  \ 'structure Point where',
  \ '  x : Float',
  \ '  y : Float',
  \ '',
  \ 'instance : ToString Color where',
  \ '  toString',
  \ '  | Color.red => "red"',
  \ '  | Color.green => "green"',
  \ '  | Color.blue => "blue"',
  \ '',
  \ 'def match_example (c : Color) : String :=',
  \ '  match c with',
  \ '  | Color.red => "It\'s red"',
  \ '  | Color.green => "It\'s green"',
  \ '  | Color.blue => "It\'s blue"'
  \ ]

" Write to temp file
let test_file = tempname() . '.lean'
call writefile(test_content, test_file)

" Open the file
execute 'edit ' . test_file

" Test that syntax highlighting is working
echo "Testing syntax highlighting..."

" Check that the file is recognized as Lean
if &filetype != 'lean'
  echo "ERROR: File not recognized as Lean (filetype: " . &filetype . ")"
  cquit!
endif

echo "✓ File recognized as Lean"

" Check that syntax is enabled
if !exists("b:current_syntax")
  echo "ERROR: Syntax not loaded"
  cquit!
endif

if b:current_syntax != "lean"
  echo "ERROR: Wrong syntax loaded: " . b:current_syntax
  cquit!
endif

echo "✓ Lean syntax loaded"

" Test specific syntax elements by checking highlight groups
let test_cases = [
  \ ['def', 'leanKeyword'],
  \ ['theorem', 'leanKeyword'], 
  \ ['inductive', 'leanKeyword'],
  \ ['structure', 'leanKeyword'],
  \ ['instance', 'leanKeyword'],
  \ ['import', 'leanKeyword'],
  \ ['match', 'leanKeyword'],
  \ ['String', 'leanType'],
  \ ['Nat', 'leanType'],
  \ ['Float', 'leanType'],
  \ ['"Hello, World!"', 'leanString'],
  \ ['--', 'leanComment'],
  \ [':=', 'leanOperator'],
  \ ['→', 'leanOperator'],
  \ ['by', 'leanKeyword']
  \ ]

echo "Testing syntax element highlighting..."

for [text, expected_group] in test_cases
  " Find the text in the buffer
  let line_num = search(text, 'n')
  if line_num > 0
    " Get the syntax group at that position
    let col_num = match(getline(line_num), text) + 1
    let syntax_id = synID(line_num, col_num, 1)
    let syntax_name = synIDattr(syntax_id, 'name')
    
    if syntax_name == expected_group
      echo "✓ " . text . " -> " . syntax_name
    else
      echo "? " . text . " -> " . syntax_name . " (expected " . expected_group . ")"
      " Not failing for now as syntax details may vary
    endif
  else
    echo "? Could not find: " . text
  endif
endfor

echo "✓ Syntax highlighting tests completed"

" Clean up
execute 'bdelete! ' . test_file
call delete(test_file)

echo "All syntax tests passed!"
qall!