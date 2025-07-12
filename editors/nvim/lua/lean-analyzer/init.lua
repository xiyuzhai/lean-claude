-- Lean Analyzer Neovim Plugin
-- Advanced Lean 4 language support with superior error messages

local M = {}

-- Default configuration
local default_config = {
  server = {
    cmd = { "lean-analyzer" },
    filetypes = { "lean" },
    root_dir = function()
      return vim.fn.getcwd()
    end,
    settings = {
      formatting = {
        enable = true,
        indentSize = 2,
        maxLineLength = 100,
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
    rename = "<leader>rn",
    find_references = "gr",
    goto_implementation = "gi",
    signature_help = "<C-k>",
    restart_server = "<leader>lr",
  },
  on_attach = function(client, bufnr)
    -- Default on_attach behavior
  end,
}

local config = vim.deepcopy(default_config)

-- Setup function
function M.setup(user_config)
  config = vim.tbl_deep_extend("force", config, user_config or {})
  
  -- Set up autocommands
  local augroup = vim.api.nvim_create_augroup("LeanAnalyzer", { clear = true })
  
  vim.api.nvim_create_autocmd("FileType", {
    group = augroup,
    pattern = "lean",
    callback = function()
      M.start_lsp()
    end,
  })
  
  -- Set up custom signs
  M.setup_signs()
  
  -- Set up custom commands
  M.setup_commands()
  
  print("Lean Analyzer initialized")
end

-- Start LSP client
function M.start_lsp()
  local lspconfig = require("lspconfig")
  local util = require("lspconfig.util")
  
  -- Create LSP configuration
  local server_config = {
    cmd = config.server.cmd,
    filetypes = config.server.filetypes,
    root_dir = config.server.root_dir,
    settings = config.server.settings,
    on_attach = function(client, bufnr)
      M.on_attach(client, bufnr)
      if config.on_attach then
        config.on_attach(client, bufnr)
      end
    end,
    capabilities = M.get_capabilities(),
    init_options = config.server.settings,
  }
  
  -- Register the server if not already registered
  if not lspconfig.lean_analyzer then
    lspconfig.lean_analyzer = {
      default_config = server_config,
    }
  end
  
  -- Start the server
  lspconfig.lean_analyzer.setup(server_config)
end

-- Get LSP capabilities
function M.get_capabilities()
  local capabilities = vim.lsp.protocol.make_client_capabilities()
  
  -- Enable completion
  capabilities.textDocument.completion.completionItem.snippetSupport = true
  capabilities.textDocument.completion.completionItem.resolveSupport = {
    properties = { "documentation", "detail", "additionalTextEdits" }
  }
  
  -- Enable inlay hints
  if config.ui.enable_inlay_hints then
    capabilities.textDocument.inlayHint = {
      dynamicRegistration = true,
    }
  end
  
  -- Enable code lens
  if config.ui.enable_code_lens then
    capabilities.textDocument.codeLens = {
      dynamicRegistration = true,
    }
  end
  
  return capabilities
end

-- LSP on_attach function
function M.on_attach(client, bufnr)
  local opts = { noremap = true, silent = true, buffer = bufnr }
  
  -- Set up keymaps if enabled
  if config.keymaps.enable then
    local keymaps = config.keymaps
    
    if keymaps.goto_definition then
      vim.keymap.set("n", keymaps.goto_definition, vim.lsp.buf.definition, opts)
    end
    
    if keymaps.hover then
      vim.keymap.set("n", keymaps.hover, vim.lsp.buf.hover, opts)
    end
    
    if keymaps.format_document then
      vim.keymap.set("n", keymaps.format_document, function()
        vim.lsp.buf.format({ async = true })
      end, opts)
    end
    
    if keymaps.code_action then
      vim.keymap.set("n", keymaps.code_action, vim.lsp.buf.code_action, opts)
    end
    
    if keymaps.rename then
      vim.keymap.set("n", keymaps.rename, vim.lsp.buf.rename, opts)
    end
    
    if keymaps.find_references then
      vim.keymap.set("n", keymaps.find_references, vim.lsp.buf.references, opts)
    end
    
    if keymaps.goto_implementation then
      vim.keymap.set("n", keymaps.goto_implementation, vim.lsp.buf.implementation, opts)
    end
    
    if keymaps.signature_help then
      vim.keymap.set("i", keymaps.signature_help, vim.lsp.buf.signature_help, opts)
    end
    
    if keymaps.restart_server then
      vim.keymap.set("n", keymaps.restart_server, function()
        M.restart()
      end, opts)
    end
  end
  
  -- Enable format on save if configured
  if client.server_capabilities.documentFormattingProvider then
    vim.api.nvim_create_autocmd("BufWritePre", {
      group = vim.api.nvim_create_augroup("LeanAnalyzerFormat", { clear = true }),
      buffer = bufnr,
      callback = function()
        vim.lsp.buf.format({ async = false })
      end,
    })
  end
  
  -- Enable inlay hints if supported
  if config.ui.enable_inlay_hints and client.server_capabilities.inlayHintProvider then
    vim.lsp.inlay_hint.enable(true, { bufnr = bufnr })
  end
  
  -- Enable code lens if supported
  if config.ui.enable_code_lens and client.server_capabilities.codeLensProvider then
    vim.lsp.codelens.refresh()
    vim.api.nvim_create_autocmd({ "BufEnter", "CursorHold", "InsertLeave" }, {
      group = vim.api.nvim_create_augroup("LeanAnalyzerCodeLens", { clear = true }),
      buffer = bufnr,
      callback = vim.lsp.codelens.refresh,
    })
  end
  
  print("Lean Analyzer attached to buffer " .. bufnr)
end

-- Setup custom signs
function M.setup_signs()
  local signs = config.ui.signs
  
  vim.fn.sign_define("DiagnosticSignError", {
    text = signs.error,
    texthl = "DiagnosticSignError",
  })
  
  vim.fn.sign_define("DiagnosticSignWarn", {
    text = signs.warning,
    texthl = "DiagnosticSignWarn",
  })
  
  vim.fn.sign_define("DiagnosticSignInfo", {
    text = signs.information,
    texthl = "DiagnosticSignInfo",
  })
  
  vim.fn.sign_define("DiagnosticSignHint", {
    text = signs.hint,
    texthl = "DiagnosticSignHint",
  })
end

-- Setup custom commands
function M.setup_commands()
  vim.api.nvim_create_user_command("LeanAnalyzerStart", function()
    M.start()
  end, { desc = "Start Lean Analyzer" })
  
  vim.api.nvim_create_user_command("LeanAnalyzerStop", function()
    M.stop()
  end, { desc = "Stop Lean Analyzer" })
  
  vim.api.nvim_create_user_command("LeanAnalyzerRestart", function()
    M.restart()
  end, { desc = "Restart Lean Analyzer" })
  
  vim.api.nvim_create_user_command("LeanAnalyzerFormat", function()
    vim.lsp.buf.format({ async = true })
  end, { desc = "Format current document" })
  
  vim.api.nvim_create_user_command("LeanAnalyzerInfo", function()
    M.show_info()
  end, { desc = "Show Lean Analyzer information" })
  
  vim.api.nvim_create_user_command("LeanAnalyzerToggleInlayHints", function()
    M.toggle_inlay_hints()
  end, { desc = "Toggle inlay hints" })
end

-- Start the language server
function M.start()
  vim.cmd("LspStart lean_analyzer")
  print("Starting Lean Analyzer...")
end

-- Stop the language server
function M.stop()
  vim.cmd("LspStop lean_analyzer")
  print("Stopped Lean Analyzer")
end

-- Restart the language server
function M.restart()
  M.stop()
  vim.defer_fn(function()
    M.start()
    print("Restarted Lean Analyzer")
  end, 1000)
end

-- Show information about the plugin
function M.show_info()
  local clients = vim.lsp.get_active_clients({ name = "lean_analyzer" })
  
  if #clients == 0 then
    print("Lean Analyzer is not running")
  else
    local client = clients[1]
    local info = {
      "Lean Analyzer Information:",
      "  Status: Running",
      "  Server ID: " .. client.id,
      "  Root Directory: " .. (client.config.root_dir or "Unknown"),
      "  Capabilities:",
      "    Completion: " .. (client.server_capabilities.completionProvider and "Yes" or "No"),
      "    Hover: " .. (client.server_capabilities.hoverProvider and "Yes" or "No"),
      "    Formatting: " .. (client.server_capabilities.documentFormattingProvider and "Yes" or "No"),
      "    Code Actions: " .. (client.server_capabilities.codeActionProvider and "Yes" or "No"),
      "    Inlay Hints: " .. (client.server_capabilities.inlayHintProvider and "Yes" or "No"),
    }
    
    print(table.concat(info, "\n"))
  end
end

-- Toggle inlay hints
function M.toggle_inlay_hints()
  local bufnr = vim.api.nvim_get_current_buf()
  if vim.lsp.inlay_hint.is_enabled({ bufnr = bufnr }) then
    vim.lsp.inlay_hint.enable(false, { bufnr = bufnr })
    print("Inlay hints disabled")
  else
    vim.lsp.inlay_hint.enable(true, { bufnr = bufnr })
    print("Inlay hints enabled")
  end
end

-- Enhanced diagnostics
function M.setup_diagnostics()
  vim.diagnostic.config({
    virtual_text = {
      prefix = "●",
      spacing = 2,
    },
    signs = true,
    underline = true,
    update_in_insert = false,
    severity_sort = true,
    float = {
      source = "always",
      border = "rounded",
      header = "",
      prefix = "",
    },
  })
  
  -- Auto open quickfix list on diagnostics
  if config.ui.auto_open_quickfix then
    vim.api.nvim_create_autocmd("DiagnosticChanged", {
      group = vim.api.nvim_create_augroup("LeanAnalyzerDiagnostics", { clear = true }),
      callback = function()
        local diagnostics = vim.diagnostic.get(0)
        if #diagnostics > 0 then
          vim.diagnostic.setqflist({ open = false })
        end
      end,
    })
  end
end

-- Utility functions for enhanced features
function M.organize_imports()
  local params = {
    command = "lean-analyzer.organizeImports",
    arguments = { vim.uri_from_bufnr(0) },
  }
  
  vim.lsp.buf.execute_command(params)
end

function M.show_error_details()
  local diagnostics = vim.diagnostic.get(0, { lnum = vim.fn.line(".") - 1 })
  
  if #diagnostics > 0 then
    local diag = diagnostics[1]
    local lines = {
      "Error Details:",
      "  Message: " .. diag.message,
      "  Source: " .. (diag.source or "Unknown"),
      "  Code: " .. (diag.code or "None"),
      "  Severity: " .. vim.diagnostic.severity[diag.severity],
    }
    
    if diag.user_data and diag.user_data.suggestions then
      table.insert(lines, "  Suggestions:")
      for _, suggestion in ipairs(diag.user_data.suggestions) do
        table.insert(lines, "    - " .. suggestion)
      end
    end
    
    vim.notify(table.concat(lines, "\n"), vim.log.levels.INFO)
  else
    vim.notify("No diagnostics at current line", vim.log.levels.INFO)
  end
end

-- Module exports
M.organize_imports = M.organize_imports
M.show_error_details = M.show_error_details
M.setup_diagnostics = M.setup_diagnostics

return M