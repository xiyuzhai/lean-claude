" Vim indent file for Lean
" Language: Lean 4

if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetLeanIndent()
setlocal indentkeys=0{,0},0),0],!^F,o,O,e,=end,=where,=by,=do

function! GetLeanIndent()
  let lnum = prevnonblank(v:lnum - 1)
  if lnum == 0
    return 0
  endif
  
  let line = getline(lnum)
  let cline = getline(v:lnum)
  let ind = indent(lnum)
  
  " Increase indent after opening brackets or keywords
  if line =~ '{\s*$\|(\s*$\|\[\s*$\|⟨\s*$'
    let ind += &shiftwidth
  endif
  
  if line =~ '\<\(do\|where\|by\|match\|with\|if\|then\|else\|let\|have\|show\)\s*$'
    let ind += &shiftwidth
  endif
  
  " Decrease indent for closing brackets
  if cline =~ '^\s*[})>\]⟩]'
    let ind -= &shiftwidth
  endif
  
  " Decrease indent for end keyword
  if cline =~ '^\s*end\>'
    let ind -= &shiftwidth
  endif
  
  " Handle case patterns
  if line =~ '^\s*|'
    let ind += &shiftwidth
  endif
  
  if cline =~ '^\s*|'
    " Find the match/with line
    let match_lnum = search('^\s*\(match\|with\)\>', 'bnW')
    if match_lnum > 0
      let ind = indent(match_lnum) + &shiftwidth
    endif
  endif
  
  return ind
endfunction