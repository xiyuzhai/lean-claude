" Lean Analyzer - Vim Plugin
" Advanced Lean 4 language support with superior error messages

if exists('g:loaded_lean_analyzer')
  finish
endif
let g:loaded_lean_analyzer = 1

" Default configuration
if !exists('g:lean_analyzer_enable')
  let g:lean_analyzer_enable = 1
endif

if !exists('g:lean_analyzer_server_path')
  let g:lean_analyzer_server_path = 'lean-analyzer'
endif

if !exists('g:lean_analyzer_auto_start')
  let g:lean_analyzer_auto_start = 1
endif

if !exists('g:lean_analyzer_format_on_save')
  let g:lean_analyzer_format_on_save = 1
endif

if !exists('g:lean_analyzer_enhanced_errors')
  let g:lean_analyzer_enhanced_errors = 1
endif

if !exists('g:lean_analyzer_import_suggestions')
  let g:lean_analyzer_import_suggestions = 1
endif

if !exists('g:lean_analyzer_completion_enable')
  let g:lean_analyzer_completion_enable = 1
endif

" Define signs
sign define lean_error text=E texthl=ErrorMsg
sign define lean_warning text=W texthl=WarningMsg
sign define lean_info text=I texthl=Question
sign define lean_hint text=H texthl=Comment

" Commands
command! LeanAnalyzerStart call lean_analyzer#start()
command! LeanAnalyzerStop call lean_analyzer#stop()
command! LeanAnalyzerRestart call lean_analyzer#restart()
command! LeanAnalyzerFormat call lean_analyzer#format()
command! LeanAnalyzerGoToDefinition call lean_analyzer#goto_definition()
command! LeanAnalyzerHover call lean_analyzer#show_hover()

" Key mappings (set up in ftplugin/lean.vim for better organization)

" Auto commands
augroup LeanAnalyzer
  autocmd!
  
  if g:lean_analyzer_auto_start
    autocmd VimEnter * call lean_analyzer#start()
  endif
  
  autocmd FileType lean call lean_analyzer#on_lean_file_open()
  autocmd BufWritePost *.lean call lean_analyzer#did_save_document()
  autocmd BufUnload *.lean call lean_analyzer#did_close_document()
  autocmd VimLeave * call lean_analyzer#stop()
augroup END