# Lean Analyzer - Vim Plugin

Traditional Vim plugin for Lean 4 with language server integration and enhanced error messages.

## Features

### 🚀 **Language Server Integration**
- **Custom LSP client** built for Vim 8+ with job support
- **Real-time diagnostics** with quickfix list integration
- **Enhanced error messages** for better learning experience
- **Code actions** and quick fixes

### 🔧 **Core Functionality**
- **Go to definition** and hover information
- **Document formatting** with configurable options
- **Import suggestions** for missing modules
- **Completion support** via omnifunc

### 🎨 **Vim Integration**
- **Custom signs** for diagnostics visualization
- **Quickfix list** for error navigation
- **Buffer-local keymaps** for Lean files only
- **Autocommands** for seamless workflow

## Installation

### Prerequisites
- **Vim 8.0+** with `+job` and `+channel` support
- **lean-analyzer** binary in PATH:
  ```bash
  cargo install --path crates/apps/lean-analyzer
  ```

### Using vim-plug
```vim
Plug 'xiyuzhai/lean-claude', {'rtp': 'editors/vim'}
```

### Using Vundle
```vim
Plugin 'xiyuzhai/lean-claude', {'rtp': 'editors/vim'}
```

### Manual Installation
```vim
" Add to your .vimrc
set runtimepath+=path/to/lean-claude/editors/vim
```

## Configuration

### Basic Configuration
```vim
" Enable Lean Analyzer
let g:lean_analyzer_enable = 1

" Server configuration
let g:lean_analyzer_server_path = 'lean-analyzer'
let g:lean_analyzer_auto_start = 1

" Feature toggles
let g:lean_analyzer_format_on_save = 1
let g:lean_analyzer_enhanced_errors = 1
let g:lean_analyzer_import_suggestions = 1
let g:lean_analyzer_completion_enable = 1

" Disable default keymaps (optional)
let g:lean_analyzer_disable_mappings = 1
```

### Advanced Configuration
```vim
" Custom server path
let g:lean_analyzer_server_path = '/usr/local/bin/lean-analyzer'

" Auto-start server when Vim starts
let g:lean_analyzer_auto_start = 1

" Format document on save
let g:lean_analyzer_format_on_save = 1

" Enable enhanced error messages for beginners
let g:lean_analyzer_enhanced_errors = 1

" Enable automatic import suggestions
let g:lean_analyzer_import_suggestions = 1

" Enable completion via omnifunc
let g:lean_analyzer_completion_enable = 1

" Custom autocommands
augroup MyLeanAnalyzer
  autocmd!
  autocmd FileType lean setlocal omnifunc=lean_analyzer#complete
  autocmd FileType lean setlocal formatprg=lean-analyzer\ format
augroup END
```

## Usage

### Commands

| Command | Description |
|---------|-------------|
| `:LeanAnalyzerStart` | Start the language server |
| `:LeanAnalyzerStop` | Stop the language server |
| `:LeanAnalyzerRestart` | Restart the language server |
| `:LeanAnalyzerFormat` | Format the current document |
| `:LeanAnalyzerGoToDefinition` | Go to symbol definition |
| `:LeanAnalyzerHover` | Show hover information |

### Default Keymaps

| Key | Mode | Action |
|-----|------|--------|
| `gd` | Normal | Go to definition |
| `K` | Normal | Show hover information |
| `<leader>f` | Normal | Format document |
| `<leader>lr` | Normal | Restart server |

### Custom Keymaps
```vim
" Custom keymaps for Lean files
augroup LeanAnalyzerKeymaps
  autocmd!
  autocmd FileType lean nnoremap <buffer> <leader>ld :LeanAnalyzerGoToDefinition<CR>
  autocmd FileType lean nnoremap <buffer> <leader>lh :LeanAnalyzerHover<CR>
  autocmd FileType lean nnoremap <buffer> <leader>lf :LeanAnalyzerFormat<CR>
  autocmd FileType lean nnoremap <buffer> <leader>ls :LeanAnalyzerStart<CR>
  autocmd FileType lean nnoremap <buffer> <leader>lt :LeanAnalyzerStop<CR>
  autocmd FileType lean nnoremap <buffer> <leader>lr :LeanAnalyzerRestart<CR>
augroup END
```

## Features in Detail

### Enhanced Error Messages
The plugin provides beginner-friendly error messages with actionable suggestions:

```lean
def f : Nat := 5  -- Error: Unknown identifier 'Nat'
                  -- Suggestion: Add 'import Std.Init.Data.Nat'
```

### Diagnostics Integration
- **Visual signs** in the sign column (E, W, I, H)
- **Quickfix list** population for easy navigation
- **Real-time updates** as you edit

### Code Actions
Basic code actions support for:
- **Import suggestions** for missing identifiers
- **Syntax fixes** for common mistakes
- **Quick fixes** for type errors

### Document Formatting
Automatic code formatting with:
- **Consistent indentation** (configurable)
- **Operator spacing** for readability
- **Import organization** and cleanup

### Completion Support
Via Vim's omnifunc mechanism:
```vim
" In insert mode, trigger completion
<C-x><C-o>
```

## Syntax Highlighting

The plugin includes comprehensive syntax highlighting for Lean 4:

- **Keywords**: `def`, `theorem`, `lemma`, `inductive`, etc.
- **Types**: `Nat`, `String`, `List`, `Prop`, `Type`
- **Operators**: `→`, `∀`, `∃`, `⟨⟩`, mathematical symbols
- **Comments**: Line (`--`) and block (`/- -/`) comments
- **Strings and numbers**: Proper escaping and formatting
- **Tactics**: `simp`, `rw`, `intro`, `apply`, etc.

## Troubleshooting

### Server Not Starting
1. **Check binary installation**:
   ```bash
   which lean-analyzer
   lean-analyzer --version
   ```

2. **Check Vim job support**:
   ```vim
   :echo has('job')  " Should return 1
   :echo has('channel')  " Should return 1
   ```

3. **Check error logs**:
   ```vim
   :messages
   ```

### No Syntax Highlighting
1. **Check filetype detection**:
   ```vim
   :set filetype?  " Should show 'lean'
   ```

2. **Force Lean filetype**:
   ```vim
   :set filetype=lean
   ```

3. **Check syntax file loading**:
   ```vim
   :syntax on
   ```

### LSP Communication Issues
1. **Check server status**:
   ```vim
   :echo job_status(s:lean_analyzer_job)
   ```

2. **Debug LSP messages** (add to .vimrc):
   ```vim
   let g:lean_analyzer_debug = 1
   ```

3. **Manual server test**:
   ```bash
   lean-analyzer --stdio
   # Should start and wait for input
   ```

### Performance Issues
1. **Disable features for large files**:
   ```vim
   autocmd BufEnter *.lean if line('$') > 1000 | let b:lean_analyzer_disable = 1 | endif
   ```

2. **Increase update time**:
   ```vim
   set updatetime=1000  " Default is 4000ms
   ```

## Development

### Plugin Structure
```
editors/vim/
├── plugin/lean-analyzer.vim    # Main plugin file
├── syntax/lean.vim            # Syntax highlighting
├── ftdetect/lean.vim          # Filetype detection
├── indent/lean.vim            # Indentation rules
└── README.md                  # This file
```

### Contributing
1. **Test changes** with a minimal vimrc:
   ```vim
   set nocompatible
   set runtimepath+=path/to/lean-claude/editors/vim
   filetype plugin indent on
   syntax on
   ```

2. **Debug LSP communication**:
   ```vim
   " Add debug prints to the plugin
   echom 'LSP message: ' . string(l:message)
   ```

3. **Test with different Vim versions**:
   ```bash
   vim --version | head -1
   ```

## Limitations

- **No inlay hints** (Vim limitation)
- **No code lens** (Vim limitation)  
- **Basic completion** compared to modern editors
- **Manual LSP implementation** may have quirks
- **Limited UI** compared to VS Code/Neovim

## Migration

### From vim-lean
```vim
" Remove old vim-lean configuration
" Plug 'leanprover/lean.vim'

" Add Lean Analyzer
Plug 'xiyuzhai/lean-claude', {'rtp': 'editors/vim'}
```

### To Neovim
Consider upgrading to the [Neovim plugin](../nvim/) for:
- Modern LSP integration
- Tree-sitter highlighting
- Better UI features
- Active development

## License

MIT License - see [LICENSE](../../LICENSE) for details.