# Lean Analyzer - Neovim Plugin

Modern Neovim plugin for Lean 4 with advanced language server features and superior error messages.

## Features

### 🚀 **LSP Integration**
- **Built on nvim-lspconfig** - Uses Neovim's native LSP client
- **Enhanced error messages** - Beginner-friendly explanations with suggestions
- **Real-time diagnostics** - Instant feedback as you type
- **Intelligent completion** - Context-aware suggestions with snippets

### 🔧 **Advanced Features**
- **Inlay hints** - Type annotations and parameter hints inline
- **Code actions** - Quick fixes and refactoring suggestions
- **Code lens** - Inline actions for theorems and definitions
- **Document formatting** - Consistent Lean code styling
- **Import organization** - Automatic import cleanup and suggestions

### 🎨 **Enhanced Editor Experience**
- **Tree-sitter integration** - Advanced syntax highlighting and navigation
- **Smart text objects** - Navigate theorems, definitions, and proofs
- **Folding support** - Fold Lean constructs intelligently
- **Custom signs** - Clear visual indicators for diagnostics

## Installation

### Prerequisites
1. **Neovim 0.8+** with LSP support
2. **lean-analyzer** binary:
   ```bash
   # From the lean-claude repository
   cargo install --path crates/apps/lean-analyzer
   ```

### Using lazy.nvim (Recommended)

```lua
{
  "xiyuzhai/lean-claude",
  dir = "/path/to/lean-claude/editors/nvim",
  ft = "lean",
  dependencies = {
    "neovim/nvim-lspconfig",
    "nvim-treesitter/nvim-treesitter",
    "nvim-treesitter/nvim-treesitter-textobjects", -- Optional
  },
  config = function()
    require("lean-analyzer").setup({
      -- Configuration options (see below)
    })
  end,
}
```

### Using packer.nvim

```lua
use {
  "xiyuzhai/lean-claude",
  rtp = "editors/nvim",
  ft = "lean",
  requires = {
    "neovim/nvim-lspconfig",
    "nvim-treesitter/nvim-treesitter",
  },
  config = function()
    require("lean-analyzer").setup()
  end,
}
```

### Manual Installation

1. Clone the repository:
   ```bash
   git clone https://github.com/xiyuzhai/lean-claude.git
   ```

2. Add to your Neovim configuration:
   ```lua
   vim.opt.rtp:prepend("/path/to/lean-claude/editors/nvim")
   require("lean-analyzer").setup()
   ```

## Configuration

### Basic Setup

```lua
require("lean-analyzer").setup({
  server = {
    cmd = { "lean-analyzer" }, -- Path to lean-analyzer binary
    settings = {
      formatting = {
        enable = true,
        indentSize = 2,
        maxLineLength = 100,
      },
      diagnostics = {
        enableEnhancedErrors = true,
      },
      importSuggestions = {
        enable = true,
      },
    },
  },
  ui = {
    auto_open_quickfix = true,
    enable_inlay_hints = true,
    enable_code_lens = true,
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

### Advanced Configuration

```lua
require("lean-analyzer").setup({
  server = {
    cmd = { "/custom/path/to/lean-analyzer", "--stdio" },
    root_dir = function()
      return vim.fn.getcwd()
    end,
    settings = {
      formatting = {
        enable = true,
        indentSize = 4,
        maxLineLength = 120,
      },
      codeActions = {
        enable = true,
      },
      diagnostics = {
        enableEnhancedErrors = true,
      },
      completion = {
        enable = true,
      },
      hover = {
        enable = true,
      },
      inlayHints = {
        enable = true,
      },
      importSuggestions = {
        enable = true,
      },
    },
  },
  ui = {
    auto_open_quickfix = false,
    enable_inlay_hints = true,
    enable_code_lens = true,
    signs = {
      error = "✗",
      warning = "⚠",
      information = "ℹ",
      hint = "💡",
    },
  },
  keymaps = {
    enable = true,
    goto_definition = "gd",
    hover = "K",
    format_document = "<leader>f",
    code_action = "<leader>ca",
    rename = "<leader>rn",
    find_references = "gr",
    goto_implementation = "gi",
    signature_help = "<C-k>",
    restart_server = "<leader>lr",
  },
  on_attach = function(client, bufnr)
    -- Custom on_attach logic
    vim.api.nvim_buf_set_option(bufnr, "omnifunc", "v:lua.vim.lsp.omnifunc")
    
    -- Set up buffer-local keymaps
    local opts = { noremap = true, silent = true, buffer = bufnr }
    vim.keymap.set("n", "<leader>d", vim.diagnostic.open_float, opts)
  end,
})
```

## Usage

### Commands

| Command | Description |
|---------|-------------|
| `:LeanAnalyzerStart` | Start the language server |
| `:LeanAnalyzerStop` | Stop the language server |
| `:LeanAnalyzerRestart` | Restart the language server |
| `:LeanAnalyzerFormat` | Format the current document |
| `:LeanAnalyzerInfo` | Show plugin information |
| `:LeanAnalyzerToggleInlayHints` | Toggle inlay hints |

### Default Keymaps

| Key | Mode | Action |
|-----|------|--------|
| `gd` | Normal | Go to definition |
| `K` | Normal | Show hover information |
| `<leader>f` | Normal | Format document |
| `<leader>ca` | Normal | Show code actions |
| `<leader>rn` | Normal | Rename symbol |
| `gr` | Normal | Find references |
| `gi` | Normal | Go to implementation |
| `<C-k>` | Insert | Show signature help |
| `<leader>lr` | Normal | Restart server |

### LSP Features

#### Enhanced Error Messages
```lean
def f : Nat := 5  -- Error with suggestion: "Import Std.Init.Data.Nat"
```

#### Code Actions
- **Add missing imports** automatically
- **Fix syntax errors** with one-click fixes
- **Organize imports** and remove unused ones
- **Extract expressions** into definitions

#### Intelligent Completion
- **Context-aware suggestions** based on current scope
- **Import completions** for missing modules
- **Snippet support** for common Lean patterns

#### Inlay Hints
```lean
def add (x: Nat) (y: Nat) : Nat := x + y
--       ^^^^ parameter hint    ^^^^ type hint
```

## Integration with Other Plugins

### Tree-sitter Integration

```lua
-- Enable tree-sitter support
require("lean-analyzer.treesitter").setup()

-- Custom text objects for Lean
vim.keymap.set({"o", "x"}, "af", "@function.outer")
vim.keymap.set({"o", "x"}, "if", "@function.inner")
vim.keymap.set({"o", "x"}, "at", "@theorem.outer")
vim.keymap.set({"o", "x"}, "it", "@theorem.inner")
```

### Telescope Integration

```lua
-- Find theorems in current file
vim.keymap.set("n", "<leader>ft", function()
  require("telescope.builtin").treesitter({
    symbols = { "theorem", "lemma" }
  })
end)

-- Search workspace symbols
vim.keymap.set("n", "<leader>fs", require("telescope.builtin").lsp_workspace_symbols)
```

### Which-key Integration

```lua
require("which-key").register({
  ["<leader>l"] = {
    name = "Lean Analyzer",
    r = { ":LeanAnalyzerRestart<CR>", "Restart Server" },
    f = { ":LeanAnalyzerFormat<CR>", "Format Document" },
    i = { ":LeanAnalyzerInfo<CR>", "Show Info" },
    h = { ":LeanAnalyzerToggleInlayHints<CR>", "Toggle Inlay Hints" },
  },
})
```

## Troubleshooting

### Server Not Starting

1. **Check binary installation**:
   ```bash
   which lean-analyzer
   lean-analyzer --version
   ```

2. **Check logs**:
   ```vim
   :LspLog
   ```

3. **Verify configuration**:
   ```lua
   :lua print(vim.inspect(require("lspconfig").lean_analyzer))
   ```

### Performance Issues

1. **Disable features for large files**:
   ```lua
   vim.api.nvim_create_autocmd("BufEnter", {
     pattern = "*.lean",
     callback = function()
       local lines = vim.api.nvim_buf_line_count(0)
       if lines > 1000 then
         vim.lsp.inlay_hint.enable(false)
       end
     end,
   })
   ```

2. **Adjust update frequency**:
   ```lua
   vim.opt.updatetime = 1000 -- Increase from default 4000ms
   ```

## Contributing

Contributions are welcome! The plugin is part of the [lean-claude](https://github.com/xiyuzhai/lean-claude) project.

### Development Setup

1. Clone the repository
2. Set up a test Neovim configuration
3. Use the plugin in development mode:
   ```lua
   vim.opt.rtp:prepend("/path/to/lean-claude/editors/nvim")
   ```

## License

MIT License - see [LICENSE](LICENSE) for details.

## Changelog

### 0.1.0
- Initial release with LSP integration
- Enhanced error messages and code actions
- Tree-sitter support
- Inlay hints and code lens
- Comprehensive keymaps and commands