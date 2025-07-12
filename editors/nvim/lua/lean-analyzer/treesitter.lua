-- Tree-sitter integration for Lean Analyzer
local M = {}

-- Tree-sitter configuration for Lean
function M.setup()
  -- Ensure tree-sitter is available
  local has_treesitter, ts_config = pcall(require, "nvim-treesitter.configs")
  if not has_treesitter then
    return
  end
  
  -- Add Lean parser configuration
  ts_config.setup({
    ensure_installed = { "lean" },
    highlight = {
      enable = true,
      additional_vim_regex_highlighting = { "lean" },
    },
    indent = {
      enable = true,
    },
    incremental_selection = {
      enable = true,
      keymaps = {
        init_selection = "gnn",
        node_incremental = "grn",
        scope_incremental = "grc",
        node_decremental = "grm",
      },
    },
    textobjects = {
      select = {
        enable = true,
        lookahead = true,
        keymaps = {
          ["af"] = "@function.outer",
          ["if"] = "@function.inner",
          ["ac"] = "@class.outer",
          ["ic"] = "@class.inner",
          ["at"] = "@theorem.outer",
          ["it"] = "@theorem.inner",
        },
      },
      move = {
        enable = true,
        set_jumps = true,
        goto_next_start = {
          ["]f"] = "@function.outer",
          ["]c"] = "@class.outer",
          ["]t"] = "@theorem.outer",
        },
        goto_next_end = {
          ["]F"] = "@function.outer",
          ["]C"] = "@class.outer",
          ["]T"] = "@theorem.outer",
        },
        goto_previous_start = {
          ["[f"] = "@function.outer",
          ["[c"] = "@class.outer",
          ["[t"] = "@theorem.outer",
        },
        goto_previous_end = {
          ["[F"] = "@function.outer",
          ["[C"] = "@class.outer",
          ["[T"] = "@theorem.outer",
        },
      },
    },
  })
end

-- Custom text objects for Lean
function M.setup_text_objects()
  local has_textobjects, textobjects = pcall(require, "nvim-treesitter.textobjects")
  if not has_textobjects then
    return
  end
  
  -- Define custom queries for Lean
  local lean_queries = {
    theorem = [[
      (theorem
        name: (identifier) @theorem.name
        body: (_) @theorem.body) @theorem.outer
    ]],
    lemma = [[
      (lemma
        name: (identifier) @lemma.name
        body: (_) @lemma.body) @lemma.outer
    ]],
    definition = [[
      (definition
        name: (identifier) @definition.name
        body: (_) @definition.body) @definition.outer
    ]],
    inductive = [[
      (inductive
        name: (identifier) @inductive.name
        constructors: (_) @inductive.constructors) @inductive.outer
    ]],
    structure = [[
      (structure
        name: (identifier) @structure.name
        fields: (_) @structure.fields) @structure.outer
    ]],
  }
  
  -- Register queries
  for name, query in pairs(lean_queries) do
    vim.treesitter.query.set("lean", name, query)
  end
end

-- Enhanced folding with tree-sitter
function M.setup_folding()
  vim.api.nvim_create_autocmd("FileType", {
    pattern = "lean",
    callback = function()
      vim.opt_local.foldmethod = "expr"
      vim.opt_local.foldexpr = "nvim_treesitter#foldexpr()"
      vim.opt_local.foldenable = false -- Start with folds open
    end,
  })
end

-- Syntax-aware commenting
function M.setup_commenting()
  local has_comment, comment = pcall(require, "Comment")
  if not has_comment then
    return
  end
  
  comment.setup({
    pre_hook = function(ctx)
      -- Use tree-sitter to determine comment style
      local node = vim.treesitter.get_node()
      if node then
        local node_type = node:type()
        if node_type == "block_comment" then
          return "/-|%-/"
        else
          return "--"
        end
      end
      return "--"
    end,
  })
end

-- Code navigation helpers
function M.goto_next_theorem()
  local ts_utils = require("nvim-treesitter.ts_utils")
  local current_node = ts_utils.get_node_at_cursor()
  
  if current_node then
    local root = ts_utils.get_root_for_node(current_node)
    local query = vim.treesitter.query.parse("lean", "(theorem) @theorem")
    
    for _, node in query:iter_captures(root, 0) do
      local start_row = node:start()
      if start_row > vim.fn.line(".") - 1 then
        vim.api.nvim_win_set_cursor(0, { start_row + 1, 0 })
        break
      end
    end
  end
end

function M.goto_prev_theorem()
  local ts_utils = require("nvim-treesitter.ts_utils")
  local current_node = ts_utils.get_node_at_cursor()
  
  if current_node then
    local root = ts_utils.get_root_for_node(current_node)
    local query = vim.treesitter.query.parse("lean", "(theorem) @theorem")
    local theorems = {}
    
    for _, node in query:iter_captures(root, 0) do
      local start_row = node:start()
      if start_row < vim.fn.line(".") - 1 then
        table.insert(theorems, start_row + 1)
      end
    end
    
    if #theorems > 0 then
      vim.api.nvim_win_set_cursor(0, { theorems[#theorems], 0 })
    end
  end
end

-- Smart selection for Lean constructs
function M.smart_select()
  local ts_utils = require("nvim-treesitter.ts_utils")
  local current_node = ts_utils.get_node_at_cursor()
  
  if current_node then
    local node_type = current_node:type()
    
    -- Expand selection based on Lean syntax
    if vim.tbl_contains({ "theorem", "lemma", "definition", "inductive" }, node_type) then
      ts_utils.select_node(current_node, "v")
    else
      -- Find parent construct
      local parent = current_node:parent()
      while parent do
        local parent_type = parent:type()
        if vim.tbl_contains({ "theorem", "lemma", "definition", "inductive" }, parent_type) then
          ts_utils.select_node(parent, "v")
          break
        end
        parent = parent:parent()
      end
    end
  end
end

return M