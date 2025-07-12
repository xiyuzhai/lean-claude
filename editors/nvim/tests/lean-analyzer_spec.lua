-- Tests for lean-analyzer Neovim plugin
-- Run with: nvim --headless -c "PlenaryBustedDirectory tests/ {minimal_init = 'tests/minimal_init.lua'}"

local lean_analyzer = require('lean-analyzer')

describe('lean-analyzer plugin', function()
  before_each(function()
    -- Reset any existing configuration
    vim.g.lean_analyzer_setup_done = nil
  end)

  describe('setup', function()
    it('should initialize with default config', function()
      lean_analyzer.setup()
      assert.truthy(vim.g.lean_analyzer_setup_done)
    end)

    it('should accept custom configuration', function()
      local custom_config = {
        server = {
          cmd = { 'custom-lean-analyzer' },
          settings = {
            formatting = {
              indentSize = 4,
            },
          },
        },
        ui = {
          auto_open_quickfix = false,
        },
      }
      
      lean_analyzer.setup(custom_config)
      assert.truthy(vim.g.lean_analyzer_setup_done)
    end)
  end)

  describe('commands', function()
    before_each(function()
      lean_analyzer.setup()
    end)

    it('should register all expected commands', function()
      local expected_commands = {
        'LeanAnalyzerStart',
        'LeanAnalyzerStop', 
        'LeanAnalyzerRestart',
        'LeanAnalyzerFormat',
        'LeanAnalyzerInfo',
        'LeanAnalyzerToggleInlayHints'
      }

      for _, cmd in ipairs(expected_commands) do
        local command_exists = vim.fn.exists(':' .. cmd) == 2
        assert.truthy(command_exists, 'Command ' .. cmd .. ' should be registered')
      end
    end)

    it('should execute commands without error', function()
      -- Test commands that should work without a server
      assert.has_no.errors(function()
        vim.cmd('LeanAnalyzerInfo')
      end)
      
      assert.has_no.errors(function()
        vim.cmd('LeanAnalyzerStop')
      end)
    end)
  end)

  describe('autocommands', function()
    before_each(function()
      lean_analyzer.setup()
    end)

    it('should set up autocommands for lean files', function()
      -- Create a test lean buffer
      local buf = vim.api.nvim_create_buf(false, true)
      vim.api.nvim_buf_set_option(buf, 'filetype', 'lean')
      vim.api.nvim_set_current_buf(buf)
      
      -- Check that autocommands are created
      local autocmds = vim.api.nvim_get_autocmds({
        group = 'LeanAnalyzer',
        buffer = buf,
      })
      
      assert.truthy(#autocmds > 0, 'Should have autocommands for lean files')
    end)
  end)

  describe('utility functions', function()
    before_each(function()
      lean_analyzer.setup()
    end)

    it('should have start/stop/restart functions', function()
      assert.truthy(type(lean_analyzer.start) == 'function')
      assert.truthy(type(lean_analyzer.stop) == 'function') 
      assert.truthy(type(lean_analyzer.restart) == 'function')
    end)

    it('should have utility functions', function()
      assert.truthy(type(lean_analyzer.show_info) == 'function')
      assert.truthy(type(lean_analyzer.toggle_inlay_hints) == 'function')
      assert.truthy(type(lean_analyzer.organize_imports) == 'function')
      assert.truthy(type(lean_analyzer.show_error_details) == 'function')
    end)

    it('should handle missing LSP client gracefully', function()
      assert.has_no.errors(function()
        lean_analyzer.show_info()
      end)
      
      assert.has_no.errors(function()
        lean_analyzer.toggle_inlay_hints()
      end)
    end)
  end)

  describe('LSP integration', function()
    before_each(function()
      lean_analyzer.setup()
    end)

    it('should configure LSP capabilities', function()
      local capabilities = lean_analyzer.get_capabilities()
      assert.truthy(capabilities)
      assert.truthy(capabilities.textDocument)
      assert.truthy(capabilities.textDocument.completion)
    end)

    it('should handle on_attach callback', function()
      local mock_client = {
        server_capabilities = {
          documentFormattingProvider = true,
          inlayHintProvider = true,
          codeLensProvider = true,
        }
      }
      
      local test_buf = vim.api.nvim_create_buf(false, true)
      vim.api.nvim_buf_set_option(test_buf, 'filetype', 'lean')
      
      assert.has_no.errors(function()
        lean_analyzer.on_attach(mock_client, test_buf)
      end)
    end)
  end)

  describe('signs and diagnostics', function()
    before_each(function()
      lean_analyzer.setup()
    end)

    it('should set up diagnostic signs', function()
      lean_analyzer.setup_signs()
      
      -- Check that signs are defined
      local signs = vim.fn.sign_getdefined()
      local sign_names = {}
      for _, sign in ipairs(signs) do
        table.insert(sign_names, sign.name)
      end
      
      assert.truthy(vim.tbl_contains(sign_names, 'DiagnosticSignError'))
      assert.truthy(vim.tbl_contains(sign_names, 'DiagnosticSignWarn'))
      assert.truthy(vim.tbl_contains(sign_names, 'DiagnosticSignInfo'))
      assert.truthy(vim.tbl_contains(sign_names, 'DiagnosticSignHint'))
    end)
  end)

  describe('keymaps', function()
    before_each(function()
      lean_analyzer.setup({
        keymaps = {
          enable = true,
          goto_definition = 'gd',
          hover = 'K',
          format_document = '<leader>f',
        }
      })
    end)

    it('should set up keymaps when enabled', function()
      local test_buf = vim.api.nvim_create_buf(false, true)
      vim.api.nvim_buf_set_option(test_buf, 'filetype', 'lean')
      vim.api.nvim_set_current_buf(test_buf)
      
      local mock_client = {
        server_capabilities = {}
      }
      
      -- Trigger on_attach to set up keymaps
      lean_analyzer.on_attach(mock_client, test_buf)
      
      -- Check that buffer-local keymaps exist
      local keymaps = vim.api.nvim_buf_get_keymap(test_buf, 'n')
      local keymap_lhs = {}
      for _, keymap in ipairs(keymaps) do
        table.insert(keymap_lhs, keymap.lhs)
      end
      
      assert.truthy(vim.tbl_contains(keymap_lhs, 'gd'))
      assert.truthy(vim.tbl_contains(keymap_lhs, 'K'))
    end)
  end)

  describe('error handling', function()
    it('should handle setup without lspconfig', function()
      -- Mock missing lspconfig
      local original_require = require
      _G.require = function(name)
        if name == 'lspconfig' then
          error('module not found')
        end
        return original_require(name)
      end
      
      assert.has_no.errors(function()
        lean_analyzer.setup()
      end)
      
      -- Restore original require
      _G.require = original_require
    end)

    it('should handle missing dependencies gracefully', function()
      assert.has_no.errors(function()
        lean_analyzer.show_error_details()
      end)
      
      assert.has_no.errors(function()
        lean_analyzer.organize_imports()
      end)
    end)
  end)
end)