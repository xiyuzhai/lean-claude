" Lean Analyzer - Autoload Functions
" Advanced Lean 4 language support with superior error messages

" Start the language server
function! lean_analyzer#start()
  if !g:lean_analyzer_enable
    return
  endif
  
  if s:lean_analyzer_job > 0
    echo 'Lean Analyzer already running'
    return
  endif
  
  echo 'Starting Lean Analyzer...'
  
  let l:opts = {
    \ 'mode': 'json',
    \ 'callback': function('s:HandleLSPMessage'),
    \ 'close_cb': function('s:OnServerClose'),
    \ 'err_cb': function('s:OnServerError'),
  \ }
  
  let s:lean_analyzer_job = job_start([g:lean_analyzer_server_path], l:opts)
  let s:lean_analyzer_channel = job_getchannel(s:lean_analyzer_job)
  
  if job_status(s:lean_analyzer_job) == 'run'
    call s:InitializeLSP()
    echo 'Lean Analyzer started successfully'
  else
    echo 'Failed to start Lean Analyzer'
  endif
endfunction

" Stop the language server
function! lean_analyzer#stop()
  if s:lean_analyzer_job > 0
    call job_stop(s:lean_analyzer_job, 'term')
    let s:lean_analyzer_job = -1
    let s:lean_analyzer_channel = -1
    let s:lean_analyzer_initialized = 0
    echo 'Lean Analyzer stopped'
  endif
endfunction

" Restart the language server
function! lean_analyzer#restart()
  call lean_analyzer#stop()
  sleep 1
  call lean_analyzer#start()
endfunction

" Formatting
function! lean_analyzer#format()
  if !s:lean_analyzer_initialized || &filetype != 'lean'
    echo 'Lean Analyzer not available for this file'
    return
  endif
  
  let l:params = {
    \ 'textDocument': {
      \ 'uri': 'file://' . expand('%:p')
    \ },
    \ 'options': {
      \ 'tabSize': &tabstop,
      \ 'insertSpaces': &expandtab
    \ }
  \ }
  
  call s:SendLSPRequest('textDocument/formatting', l:params, function('s:ApplyTextEdits'))
endfunction

" Go to definition
function! lean_analyzer#goto_definition()
  if !s:lean_analyzer_initialized || &filetype != 'lean'
    echo 'Lean Analyzer not available for this file'
    return
  endif
  
  let l:params = {
    \ 'textDocument': {
      \ 'uri': 'file://' . expand('%:p')
    \ },
    \ 'position': {
      \ 'line': line('.') - 1,
      \ 'character': col('.') - 1
    \ }
  \ }
  
  call s:SendLSPRequest('textDocument/definition', l:params, function('s:HandleDefinitionResponse'))
endfunction

" Show hover information
function! lean_analyzer#show_hover()
  if !s:lean_analyzer_initialized || &filetype != 'lean'
    return
  endif
  
  let l:params = {
    \ 'textDocument': {
      \ 'uri': 'file://' . expand('%:p')
    \ },
    \ 'position': {
      \ 'line': line('.') - 1,
      \ 'character': col('.') - 1
    \ }
  \ }
  
  call s:SendLSPRequest('textDocument/hover', l:params, function('s:HandleHoverResponse'))
endfunction

" Completion function
function! lean_analyzer#complete(findstart, base)
  if a:findstart
    let l:line = getline('.')
    let l:start = col('.') - 1
    while l:start > 0 && l:line[l:start - 1] =~ '\w'
      let l:start -= 1
    endwhile
    return l:start
  else
    " TODO: Implement LSP completion request
    return []
  endif
endfunction

" ===== SCRIPT-LOCAL FUNCTIONS =====
" These functions need access to script-local variables

" Global variables for LSP client (script-local in autoload)
let s:lean_analyzer_job = -1
let s:lean_analyzer_channel = -1
let s:lean_analyzer_initialized = 0
let s:request_id = 0
let s:pending_requests = {}
let s:diagnostics = {}

" Initialize LSP
function! s:InitializeLSP()
  let l:root_uri = 'file://' . getcwd()
  let l:init_params = {
    \ 'processId': getpid(),
    \ 'rootUri': l:root_uri,
    \ 'capabilities': {
      \ 'textDocument': {
        \ 'completion': {'dynamicRegistration': v:false},
        \ 'hover': {'dynamicRegistration': v:false},
        \ 'signatureHelp': {'dynamicRegistration': v:false},
        \ 'definition': {'dynamicRegistration': v:false},
        \ 'references': {'dynamicRegistration': v:false},
        \ 'documentHighlight': {'dynamicRegistration': v:false},
        \ 'documentSymbol': {'dynamicRegistration': v:false},
        \ 'codeAction': {'dynamicRegistration': v:false},
        \ 'formatting': {'dynamicRegistration': v:false},
        \ 'publishDiagnostics': {'relatedInformation': v:true}
      \ },
      \ 'workspace': {
        \ 'workspaceFolders': v:true
      \ }
    \ },
    \ 'initializationOptions': {
      \ 'formatting': {'enable': v:true},
      \ 'codeActions': {'enable': v:true},
      \ 'diagnostics': {'enableEnhancedErrors': g:lean_analyzer_enhanced_errors},
      \ 'importSuggestions': {'enable': g:lean_analyzer_import_suggestions}
    \ }
  \ }
  
  call s:SendLSPRequest('initialize', l:init_params, function('s:OnInitializeResponse'))
endfunction

function! s:OnInitializeResponse(response)
  if has_key(a:response, 'result')
    let s:lean_analyzer_initialized = 1
    call s:SendLSPNotification('initialized', {})
    echo 'Lean Analyzer initialized'
  else
    echo 'Failed to initialize Lean Analyzer'
  endif
endfunction

function! s:OnServerClose(channel)
  echo 'Lean Analyzer server closed'
  let s:lean_analyzer_job = -1
  let s:lean_analyzer_channel = -1
  let s:lean_analyzer_initialized = 0
endfunction

function! s:OnServerError(channel, msg)
  echom 'Lean Analyzer error: ' . a:msg
endfunction

" LSP communication functions
function! s:SendLSPRequest(method, params, callback)
  if s:lean_analyzer_channel < 0
    return
  endif
  
  let s:request_id += 1
  let l:request = {
    \ 'jsonrpc': '2.0',
    \ 'id': s:request_id,
    \ 'method': a:method,
    \ 'params': a:params
  \ }
  
  let s:pending_requests[s:request_id] = a:callback
  call ch_sendraw(s:lean_analyzer_channel, json_encode(l:request) . "\r\n")
endfunction

function! s:SendLSPNotification(method, params)
  if s:lean_analyzer_channel < 0
    return
  endif
  
  let l:notification = {
    \ 'jsonrpc': '2.0',
    \ 'method': a:method,
    \ 'params': a:params
  \ }
  
  call ch_sendraw(s:lean_analyzer_channel, json_encode(l:notification) . "\r\n")
endfunction

" LSP message handling
function! s:HandleLSPMessage(channel, msg)
  try
    let l:message = json_decode(a:msg)
    
    if has_key(l:message, 'id') && has_key(s:pending_requests, l:message.id)
      " Response to a request
      let l:callback = s:pending_requests[l:message.id]
      unlet s:pending_requests[l:message.id]
      call l:callback(l:message)
    elseif has_key(l:message, 'method')
      " Notification or request from server
      if l:message.method == 'textDocument/publishDiagnostics'
        call s:UpdateDiagnostics(l:message.params)
      endif
    endif
  catch
    echom 'Error parsing LSP message: ' . v:exception
  endtry
endfunction

function! s:ApplyTextEdits(response)
  if has_key(a:response, 'result') && len(a:response.result) > 0
    let l:save_cursor = getpos('.')
    for l:edit in reverse(a:response.result)
      let l:start_line = l:edit.range.start.line + 1
      let l:end_line = l:edit.range.end.line + 1
      let l:start_col = l:edit.range.start.character + 1
      let l:end_col = l:edit.range.end.character + 1
      
      " Replace text
      call setline(l:start_line, strpart(getline(l:start_line), 0, l:start_col - 1) . 
                 \ l:edit.newText . strpart(getline(l:end_line), l:end_col - 1))
      
      " Remove additional lines if needed
      if l:end_line > l:start_line
        execute (l:start_line + 1) . ',' . l:end_line . 'delete'
      endif
    endfor
    call setpos('.', l:save_cursor)
    echo 'Document formatted'
  endif
endfunction

function! s:HandleDefinitionResponse(response)
  if has_key(a:response, 'result') && len(a:response.result) > 0
    let l:location = a:response.result[0]
    let l:uri = l:location.uri
    let l:range = l:location.range
    
    " Convert file:// URI to file path
    let l:file = substitute(l:uri, '^file://', '', '')
    
    execute 'edit ' . l:file
    call cursor(l:range.start.line + 1, l:range.start.character + 1)
  else
    echo 'Definition not found'
  endif
endfunction

function! s:HandleHoverResponse(response)
  if has_key(a:response, 'result') && has_key(a:response.result, 'contents')
    let l:contents = a:response.result.contents
    if type(l:contents) == type([])
      echo join(l:contents, "\n")
    else
      echo l:contents
    endif
  endif
endfunction

function! s:UpdateDiagnostics(params)
  let l:uri = a:params.uri
  let l:diagnostics = a:params.diagnostics
  let s:diagnostics[l:uri] = l:diagnostics
  
  " Clear existing signs
  execute 'sign unplace * file=' . expand('%:p')
  
  " Place new signs
  for l:diag in l:diagnostics
    let l:line = l:diag.range.start.line + 1
    let l:severity = get(l:diag, 'severity', 1)
    let l:sign_name = 'lean_error'
    
    if l:severity == 2
      let l:sign_name = 'lean_warning'
    elseif l:severity == 3
      let l:sign_name = 'lean_info'
    elseif l:severity == 4
      let l:sign_name = 'lean_hint'
    endif
    
    execute 'sign place ' . l:line . ' line=' . l:line . ' name=' . l:sign_name . ' file=' . expand('%:p')
  endfor
  
  call s:UpdateQuickfixList()
endfunction

function! s:UpdateQuickfixList()
  let l:qf_list = []
  for [l:uri, l:diagnostics] in items(s:diagnostics)
    let l:file = substitute(l:uri, '^file://', '', '')
    for l:diag in l:diagnostics
      let l:line = l:diag.range.start.line + 1
      let l:col = l:diag.range.start.character + 1
      let l:type = 'E'
      if get(l:diag, 'severity', 1) > 1
        let l:type = 'W'
      endif
      
      call add(l:qf_list, {
        \ 'filename': l:file,
        \ 'lnum': l:line,
        \ 'col': l:col,
        \ 'text': l:diag.message,
        \ 'type': l:type
      \ })
    endfor
  endfor
  
  call setqflist(l:qf_list)
endfunction

" Document synchronization functions
function! lean_analyzer#did_open_document()
  if !s:lean_analyzer_initialized || &filetype != 'lean'
    return
  endif
  
  let l:params = {
    \ 'textDocument': {
      \ 'uri': 'file://' . expand('%:p'),
      \ 'languageId': 'lean4',
      \ 'version': 1,
      \ 'text': join(getline(1, '$'), "\n")
    \ }
  \ }
  
  call s:SendLSPNotification('textDocument/didOpen', l:params)
endfunction

function! lean_analyzer#did_change_document()
  if !s:lean_analyzer_initialized || &filetype != 'lean'
    return
  endif
  
  let l:params = {
    \ 'textDocument': {
      \ 'uri': 'file://' . expand('%:p'),
      \ 'version': b:document_version + 1
    \ },
    \ 'contentChanges': [{
      \ 'text': join(getline(1, '$'), "\n")
    \ }]
  \ }
  
  let b:document_version += 1
  call s:SendLSPNotification('textDocument/didChange', l:params)
endfunction

function! lean_analyzer#did_save_document()
  if !s:lean_analyzer_initialized || &filetype != 'lean'
    return
  endif
  
  let l:params = {
    \ 'textDocument': {
      \ 'uri': 'file://' . expand('%:p')
    \ },
    \ 'text': join(getline(1, '$'), "\n")
  \ }
  
  call s:SendLSPNotification('textDocument/didSave', l:params)
endfunction

function! lean_analyzer#did_close_document()
  if !s:lean_analyzer_initialized || &filetype != 'lean'
    return
  endif
  
  let l:params = {
    \ 'textDocument': {
      \ 'uri': 'file://' . expand('%:p')
    \ }
  \ }
  
  call s:SendLSPNotification('textDocument/didClose', l:params)
endfunction

function! lean_analyzer#on_lean_file_open()
  let b:document_version = 1
  call lean_analyzer#did_open_document()
  
  if g:lean_analyzer_format_on_save
    autocmd BufWritePre <buffer> call lean_analyzer#format()
  endif
  
  " Set up buffer-local completion
  if g:lean_analyzer_completion_enable && exists('&omnifunc')
    setlocal omnifunc=lean_analyzer#complete
  endif
  
  " Set up text change monitoring
  autocmd TextChanged,TextChangedI <buffer> call lean_analyzer#did_change_document()
endfunction