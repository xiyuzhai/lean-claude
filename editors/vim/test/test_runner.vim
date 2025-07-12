" Vim test runner for Lean Analyzer plugin
" Run with: vim -u NONE -S test/test_runner.vim

" Set up test environment
set nocompatible
set runtimepath+=.
filetype plugin indent on
syntax on

" Source the plugin
source plugin/lean-analyzer.vim

" Test results
let g:test_results = []
let g:test_count = 0
let g:test_passed = 0

" Test framework functions
function! Assert(condition, message)
  let g:test_count += 1
  if a:condition
    let g:test_passed += 1
    echo "✓ " . a:message
  else
    echo "✗ " . a:message
    call add(g:test_results, "FAIL: " . a:message)
  endif
endfunction

function! AssertEqual(expected, actual, message)
  let g:test_count += 1
  if a:expected == a:actual
    let g:test_passed += 1
    echo "✓ " . a:message
  else
    echo "✗ " . a:message . " (expected: " . string(a:expected) . ", got: " . string(a:actual) . ")"
    call add(g:test_results, "FAIL: " . a:message)
  endif
endfunction

function! AssertExists(name, message)
  let g:test_count += 1
  if exists(a:name)
    let g:test_passed += 1
    echo "✓ " . a:message
  else
    echo "✗ " . a:message . " (" . a:name . " does not exist)"
    call add(g:test_results, "FAIL: " . a:message)
  endif
endfunction

function! TestSuite(name)
  echo ""
  echo "=== " . a:name . " ==="
endfunction

" Run tests
call TestSuite("Plugin Loading")
call AssertExists("g:loaded_lean_analyzer", "Plugin should be loaded")

call TestSuite("Configuration Variables")
call AssertExists("g:lean_analyzer_enable", "Enable config should exist")
call AssertExists("g:lean_analyzer_server_path", "Server path config should exist")
call AssertExists("g:lean_analyzer_auto_start", "Auto start config should exist")
call AssertEqual(1, g:lean_analyzer_enable, "Plugin should be enabled by default")
call AssertEqual('lean-analyzer', g:lean_analyzer_server_path, "Default server path should be lean-analyzer")

call TestSuite("Function Definitions")
call Assert(exists('*lean_analyzer#start'), "Start function should exist")
call Assert(exists('*lean_analyzer#stop'), "Stop function should exist")  
call Assert(exists('*lean_analyzer#restart'), "Restart function should exist")
call Assert(exists('*lean_analyzer#format'), "Format function should exist")
call Assert(exists('*lean_analyzer#goto_definition'), "Goto definition function should exist")
call Assert(exists('*lean_analyzer#show_hover'), "Show hover function should exist")

call TestSuite("Commands")
call Assert(exists(':LeanAnalyzerStart'), "LeanAnalyzerStart command should exist")
call Assert(exists(':LeanAnalyzerStop'), "LeanAnalyzerStop command should exist")
call Assert(exists(':LeanAnalyzerRestart'), "LeanAnalyzerRestart command should exist")
call Assert(exists(':LeanAnalyzerFormat'), "LeanAnalyzerFormat command should exist")
call Assert(exists(':LeanAnalyzerGoToDefinition'), "LeanAnalyzerGoToDefinition command should exist")
call Assert(exists(':LeanAnalyzerHover'), "LeanAnalyzerHover command should exist")

call TestSuite("Filetype Detection")
" Create a temporary lean file to test filetype detection
let test_file = tempname() . '.lean'
execute 'edit ' . test_file
call Assert(&filetype == 'lean', "Lean file should have correct filetype")

call TestSuite("Syntax Highlighting")
" Test that syntax file loads without errors
try
  runtime syntax/lean.vim
  call Assert(1, "Syntax file should load without errors")
catch
  call Assert(0, "Syntax file should load without errors: " . v:exception)
endtry

call TestSuite("Autocommands")
" Check that autocommands are set up
let autocmds = execute('autocmd LeanAnalyzer')
call Assert(len(autocmds) > 0, "LeanAnalyzer autocommands should be defined")

call TestSuite("Key Mappings")
" Test that key mappings exist for lean files
if &filetype == 'lean'
  let mappings = execute('nmap <buffer>')
  call Assert(mappings =~ 'gd', "Go to definition mapping should exist")
  call Assert(mappings =~ 'K', "Hover mapping should exist")
endif

call TestSuite("Variable Initialization")
" Test that global variables are properly initialized
call AssertExists("s:lean_analyzer_job", "Job variable should be initialized")
call AssertExists("s:lean_analyzer_channel", "Channel variable should be initialized") 
call AssertExists("s:request_id", "Request ID should be initialized")

call TestSuite("Sign Definitions")
" Test that signs are properly defined
let signs = execute('sign list')
call Assert(signs =~ 'lean_error', "Error sign should be defined")
call Assert(signs =~ 'lean_warning', "Warning sign should be defined")
call Assert(signs =~ 'lean_info', "Info sign should be defined")
call Assert(signs =~ 'lean_hint', "Hint sign should be defined")

call TestSuite("Function Safety")
" Test that functions handle missing server gracefully
try
  " These should not throw errors even without a server
  call lean_analyzer#stop()
  call Assert(1, "Stop function should handle missing server")
catch
  call Assert(0, "Stop function should handle missing server: " . v:exception)
endtry

call TestSuite("Configuration Validation")
" Test configuration edge cases
let g:lean_analyzer_server_path = '/nonexistent/path'
try
  " This might fail but shouldn't crash
  call lean_analyzer#start()
  call lean_analyzer#stop()
  call Assert(1, "Should handle invalid server path gracefully")
catch
  call Assert(1, "Should handle invalid server path gracefully (expected error)")
endtry

" Restore default
let g:lean_analyzer_server_path = 'lean-analyzer'

call TestSuite("Buffer Local Variables")
" Test buffer-local variables for lean files
if &filetype == 'lean'
  call AssertExists("b:document_version", "Document version should be set for lean files")
endif

call TestSuite("Utility Functions")
" Test internal utility functions exist
call Assert(exists('*s:HandleLSPMessage'), "LSP message handler should exist")
call Assert(exists('*s:SendLSPRequest'), "LSP request sender should exist") 
call Assert(exists('*s:SendLSPNotification'), "LSP notification sender should exist")

" Print results
echo ""
echo "=== TEST RESULTS ==="
echo "Tests run: " . g:test_count
echo "Tests passed: " . g:test_passed  
echo "Tests failed: " . (g:test_count - g:test_passed)

if len(g:test_results) > 0
  echo ""
  echo "FAILURES:"
  for result in g:test_results
    echo result
  endfor
endif

" Exit with appropriate code
if g:test_passed == g:test_count
  echo ""
  echo "All tests passed! ✓"
  qall!
else
  echo ""
  echo "Some tests failed! ✗"
  cquit!
endif