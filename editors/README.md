# Editor Integrations for Lean Analyzer

This directory contains editor plugins and extensions for the Lean Analyzer language server, providing advanced Lean 4 support with superior error messages and rust-analyzer-like features.

## Available Editors

### 🆚 [VS Code Extension](./vscode/)
- **Full-featured** VS Code extension with LSP integration
- **Enhanced UI** with status bar, command palette, and settings
- **Built-in themes** and syntax highlighting
- **Code lenses** and inlay hints
- **Auto-installation** workflow

### 📝 [Vim Plugin](./vim/)
- **Traditional Vim** support with LSP client
- **Custom signs** and quickfix integration
- **Manual LSP** implementation for compatibility
- **Lightweight** and fast startup

### 🌙 [Neovim Plugin](./nvim/)
- **Modern LSP integration** using nvim-lspconfig
- **Tree-sitter support** for advanced syntax highlighting
- **Lua configuration** with extensive customization
- **Plugin ecosystem** integration (Telescope, Which-key, etc.)

## Quick Start Guide

### 1. Install Lean Analyzer

First, install the lean-analyzer language server:

```bash
# From the lean-claude repository root
cargo install --path crates/apps/lean-analyzer

# Verify installation
lean-analyzer --version
```

### 2. Choose Your Editor

#### VS Code (Recommended for beginners)
```bash
cd editors/vscode
npm install
npm run package
code --install-extension lean-analyzer-0.1.0.vsix
```

#### Vim
```vim
" Add to your .vimrc
set runtimepath+=path/to/lean-claude/editors/vim
```

#### Neovim
```lua
-- Using lazy.nvim
{
  "xiyuzhai/lean-claude",
  dir = "path/to/lean-claude/editors/nvim",
  ft = "lean",
  dependencies = { "neovim/nvim-lspconfig" },
  config = function()
    require("lean-analyzer").setup()
  end,
}
```

## Features Comparison

| Feature | VS Code | Vim | Neovim |
|---------|---------|-----|--------|
| **LSP Integration** | ✅ Full | ✅ Manual | ✅ Native |
| **Syntax Highlighting** | ✅ Rich | ✅ Basic | ✅ Tree-sitter |
| **Error Messages** | ✅ Enhanced | ✅ Basic | ✅ Enhanced |
| **Code Actions** | ✅ Full UI | ✅ Basic | ✅ Full |
| **Completion** | ✅ Rich | ✅ Basic | ✅ Rich |
| **Formatting** | ✅ Auto | ✅ Manual | ✅ Auto |
| **Inlay Hints** | ✅ Yes | ❌ No | ✅ Yes |
| **Code Lens** | ✅ Yes | ❌ No | ✅ Yes |
| **Debugging** | ✅ Integrated | ❌ No | ⚠️ External |
| **Extensions** | ✅ Marketplace | ✅ Plugin | ✅ Plugin |

## Key Features Across All Editors

### 🚀 **Enhanced Error Messages**
All editors provide beginner-friendly error explanations:

```lean
def f : Nat := 5  -- Error: Unknown identifier 'Nat'
                  -- 💡 Quick fix: Add 'import Std.Init.Data.Nat'
```

### 🔧 **Smart Code Actions**
- **Import suggestions** for missing modules
- **Syntax fixes** for common mistakes  
- **Type annotations** when inference fails
- **Refactoring actions** for code improvement

### 📊 **Real-time Diagnostics**
- **Instant feedback** as you type
- **Contextual suggestions** based on code context
- **Progressive error** explanations for learning

### 🎨 **Advanced Language Support**
- **Go to definition** and find references
- **Hover information** with documentation
- **Symbol search** across workspace
- **Intelligent completion** with snippets

## Installation Guides

### VS Code Extension

1. **Prerequisites**:
   - VS Code 1.74.0+
   - lean-analyzer binary in PATH

2. **Install from VSIX**:
   ```bash
   cd editors/vscode
   npm install
   npm run package
   code --install-extension lean-analyzer-0.1.0.vsix
   ```

3. **Configure** (optional):
   ```json
   {
     "leanAnalyzer.serverPath": "/custom/path/to/lean-analyzer",
     "leanAnalyzer.formatting.indentSize": 4,
     "leanAnalyzer.diagnostics.enableEnhancedErrors": true
   }
   ```

### Vim Plugin

1. **Prerequisites**:
   - Vim 8.0+ with job support
   - lean-analyzer binary in PATH

2. **Install with vim-plug**:
   ```vim
   Plug 'xiyuzhai/lean-claude', {'rtp': 'editors/vim'}
   ```

3. **Manual installation**:
   ```vim
   " Add to .vimrc
   set runtimepath+=path/to/lean-claude/editors/vim
   ```

4. **Configure**:
   ```vim
   let g:lean_analyzer_server_path = '/custom/path/to/lean-analyzer'
   let g:lean_analyzer_format_on_save = 1
   let g:lean_analyzer_enhanced_errors = 1
   ```

### Neovim Plugin

1. **Prerequisites**:
   - Neovim 0.8+
   - nvim-lspconfig
   - lean-analyzer binary in PATH

2. **Install with lazy.nvim**:
   ```lua
   {
     "xiyuzhai/lean-claude",
     dir = "path/to/lean-claude/editors/nvim",
     ft = "lean",
     dependencies = {
       "neovim/nvim-lspconfig",
       "nvim-treesitter/nvim-treesitter",
     },
     config = function()
       require("lean-analyzer").setup()
     end,
   }
   ```

3. **Install with packer**:
   ```lua
   use {
     "xiyuzhai/lean-claude",
     rtp = "editors/nvim",
     ft = "lean",
     requires = { "neovim/nvim-lspconfig" },
     config = function()
       require("lean-analyzer").setup()
     end,
   }
   ```

## Configuration Examples

### VS Code Settings
```json
{
  "leanAnalyzer.enable": true,
  "leanAnalyzer.serverPath": "lean-analyzer",
  "leanAnalyzer.formatting.enable": true,
  "leanAnalyzer.formatting.indentSize": 2,
  "leanAnalyzer.formatting.maxLineLength": 100,
  "leanAnalyzer.codeActions.enable": true,
  "leanAnalyzer.diagnostics.enableEnhancedErrors": true,
  "leanAnalyzer.importSuggestions.enable": true,
  "leanAnalyzer.completion.enable": true,
  "leanAnalyzer.hover.enable": true,
  "leanAnalyzer.inlayHints.enable": true
}
```

### Vim Configuration
```vim
" Basic configuration
let g:lean_analyzer_enable = 1
let g:lean_analyzer_server_path = 'lean-analyzer'
let g:lean_analyzer_auto_start = 1
let g:lean_analyzer_format_on_save = 1
let g:lean_analyzer_enhanced_errors = 1
let g:lean_analyzer_import_suggestions = 1
let g:lean_analyzer_completion_enable = 1

" Custom keymaps
nnoremap <buffer> gd :LeanAnalyzerGoToDefinition<CR>
nnoremap <buffer> K :LeanAnalyzerHover<CR>
nnoremap <buffer> <leader>f :LeanAnalyzerFormat<CR>
nnoremap <buffer> <leader>lr :LeanAnalyzerRestart<CR>
```

### Neovim Configuration
```lua
require("lean-analyzer").setup({
  server = {
    cmd = { "lean-analyzer" },
    settings = {
      formatting = {
        enable = true,
        indentSize = 2,
        maxLineLength = 100,
      },
      codeActions = { enable = true },
      diagnostics = { enableEnhancedErrors = true },
      importSuggestions = { enable = true },
    },
  },
  ui = {
    auto_open_quickfix = true,
    enable_inlay_hints = true,
    enable_code_lens = true,
    signs = {
      error = "E",
      warning = "W", 
      information = "I",
      hint = "H",
    },
  },
  keymaps = {
    enable = true,
    goto_definition = "gd",
    hover = "K",
    format_document = "<leader>f",
    code_action = "<leader>ca",
    restart_server = "<leader>lr",
  },
})
```

## Usage Examples

### Basic Lean Development

1. **Create a new Lean file**:
   ```lean
   -- hello.lean
   def hello (name : String) : String := 
     "Hello, " ++ name
   
   #eval hello "World"
   ```

2. **Get enhanced error messages**:
   ```lean
   def broken : Nat := 5  -- Error with import suggestion
   ```

3. **Use code actions**:
   - Place cursor on error
   - Trigger code action (Ctrl+. in VS Code, `<leader>ca` in Neovim)
   - Select "Add import Std.Init.Data.Nat"

### Advanced Features

1. **Go to definition**:
   - Place cursor on any identifier
   - Press `gd` to jump to definition

2. **Find references**:
   - Press `gr` to find all references to symbol

3. **Format document**:
   - Press `<leader>f` to format current file

4. **Organize imports**:
   - Use command palette: "Lean Analyzer: Organize Imports"

## Troubleshooting

### Common Issues

1. **Language server not found**:
   ```bash
   # Ensure lean-analyzer is in PATH
   which lean-analyzer
   
   # Or set custom path in editor settings
   ```

2. **No syntax highlighting**:
   - Check file extension is `.lean`
   - Verify editor language mode is set to "Lean 4"

3. **LSP not starting**:
   - Check editor LSP logs
   - Verify lean-analyzer version compatibility
   - Restart editor/language server

### Performance Optimization

1. **Large files**:
   - Disable inlay hints for files >1000 lines
   - Reduce update frequency in editor settings

2. **Memory usage**:
   - Restart language server periodically
   - Close unused Lean files

3. **Startup time**:
   - Use lazy loading in plugin managers
   - Defer non-essential features

## Support and Contributing

- **Issues**: [GitHub Issues](https://github.com/xiyuzhai/lean-claude/issues)
- **Discussions**: [GitHub Discussions](https://github.com/xiyuzhai/lean-claude/discussions)
- **Contributing**: See individual editor README files for development setup

## License

MIT License - see [LICENSE](../LICENSE) for details.