" Lean filetype plugin
" Sets up buffer-local settings and key mappings for Lean files

if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

" Key mappings
if !exists('g:lean_analyzer_disable_mappings') || !g:lean_analyzer_disable_mappings
  nnoremap <buffer> gd :LeanAnalyzerGoToDefinition<CR>
  nnoremap <buffer> K :LeanAnalyzerHover<CR>
  nnoremap <buffer> <leader>f :LeanAnalyzerFormat<CR>
  nnoremap <buffer> <leader>lr :LeanAnalyzerRestart<CR>
endif

" Set comment string for Lean
setlocal commentstring=--\ %s

" Set indentation
setlocal expandtab
setlocal tabstop=2
setlocal shiftwidth=2
setlocal softtabstop=2

" Allow undo of ftplugin changes
let b:undo_ftplugin = 'setlocal commentstring< expandtab< tabstop< shiftwidth< softtabstop<'