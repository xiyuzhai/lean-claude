-- Lean Analyzer Neovim Plugin Entry Point

-- Ensure the plugin is only loaded once
if vim.g.loaded_lean_analyzer then
  return
end
vim.g.loaded_lean_analyzer = 1

-- Check for required dependencies
local has_lspconfig, _ = pcall(require, "lspconfig")
if not has_lspconfig then
  vim.notify("lean-analyzer.nvim requires nvim-lspconfig", vim.log.levels.ERROR)
  return
end

-- Setup autocommands for lazy loading
local augroup = vim.api.nvim_create_augroup("LeanAnalyzerSetup", { clear = true })

vim.api.nvim_create_autocmd("FileType", {
  group = augroup,
  pattern = "lean",
  once = true,
  callback = function()
    -- Load the main module when a Lean file is opened
    local lean_analyzer = require("lean-analyzer")
    
    -- Use default configuration if not already set up
    if not vim.g.lean_analyzer_setup_done then
      lean_analyzer.setup()
      vim.g.lean_analyzer_setup_done = true
    end
  end,
})

-- Global command to manually setup if needed
vim.api.nvim_create_user_command("LeanAnalyzerSetup", function(opts)
  local config = {}
  
  -- Parse any arguments as Lua code
  if opts.args and opts.args ~= "" then
    local ok, parsed_config = pcall(loadstring("return " .. opts.args))
    if ok and type(parsed_config) == "table" then
      config = parsed_config
    end
  end
  
  require("lean-analyzer").setup(config)
  vim.g.lean_analyzer_setup_done = true
  print("Lean Analyzer setup completed")
end, {
  nargs = "?",
  desc = "Setup Lean Analyzer with optional configuration",
  complete = function()
    return { "{ server = { cmd = { 'lean-analyzer' } } }" }
  end,
})