# Lean Analyzer - VS Code Extension

Advanced Lean 4 language support with superior error messages and rust-analyzer-like features.

## Features

### 🚀 **Enhanced Error Messages**
- **Beginner-friendly error explanations** - Clear, actionable error messages that explain what went wrong and how to fix it
- **Contextual suggestions** - Smart suggestions based on the code context (theorems, definitions, types)
- **Import assistance** - Automatic detection and suggestions for missing imports

### 🔧 **Rust-analyzer-like Features**
- **Quick fixes and code actions** - One-click fixes for common issues
- **Import organization** - Automatic import sorting and cleanup
- **Smart completions** - Intelligent code completion with type information
- **Inlay hints** - Type annotations and parameter hints
- **Code formatting** - Consistent code styling with configurable options

### 📊 **Advanced Language Support**
- **Real-time diagnostics** - Instant error checking as you type
- **Hover information** - Detailed type and documentation on hover
- **Go to definition** - Navigate to symbol definitions
- **Find references** - Find all usages of symbols
- **Symbol search** - Workspace-wide symbol navigation

### 🎨 **Enhanced Editor Experience**
- **Syntax highlighting** - Rich syntax highlighting for Lean 4
- **Code lenses** - Inline actions for theorems and definitions
- **Snippets** - Common Lean patterns and templates
- **Bracket matching** - Smart bracket pairing including ⟨⟩
- **Auto-indentation** - Intelligent indentation rules

## Installation

### Prerequisites
1. **Install VS Code** (version 1.74.0 or later)
2. **Install lean-analyzer**: 
   ```bash
   # From the lean-claude repository
   cargo install --path crates/apps/lean-analyzer
   ```

### Install the Extension
1. Open VS Code
2. Go to Extensions (Ctrl+Shift+X)
3. Search for "Lean Analyzer"
4. Click Install

Or install from VSIX:
```bash
# Package the extension
npm run package
# Install the generated .vsix file
code --install-extension lean-analyzer-0.1.0.vsix
```

## Configuration

The extension can be configured through VS Code settings. Go to **Settings** → **Extensions** → **Lean Analyzer**.

### Key Settings

| Setting | Default | Description |
|---------|---------|-------------|
| `leanAnalyzer.enable` | `true` | Enable/disable the language server |
| `leanAnalyzer.serverPath` | `""` | Path to lean-analyzer executable |
| `leanAnalyzer.formatting.enable` | `true` | Enable automatic formatting |
| `leanAnalyzer.formatting.indentSize` | `2` | Number of spaces for indentation |
| `leanAnalyzer.codeActions.enable` | `true` | Enable quick fixes and code actions |
| `leanAnalyzer.diagnostics.enableEnhancedErrors` | `true` | Enable beginner-friendly error messages |
| `leanAnalyzer.importSuggestions.enable` | `true` | Enable automatic import suggestions |

### Example Configuration
```json
{
  "leanAnalyzer.formatting.indentSize": 4,
  "leanAnalyzer.formatting.maxLineLength": 120,
  "leanAnalyzer.diagnostics.enableEnhancedErrors": true,
  "leanAnalyzer.importSuggestions.enable": true
}
```

## Commands

| Command | Keybinding | Description |
|---------|------------|-------------|
| `Lean Analyzer: Restart` | `Ctrl+Shift+P` | Restart the language server |
| `Lean Analyzer: Format Document` | `Shift+Alt+F` | Format the current document |
| `Lean Analyzer: Organize Imports` | `Shift+Alt+O` | Organize and clean up imports |
| `Lean Analyzer: Check File` | - | Check the current file for errors |
| `Lean Analyzer: Show Output` | - | Show the language server output |
| `Lean Analyzer: Show Error Details` | - | Show detailed error information |

## Usage Examples

### Smart Error Messages
When you write incorrect Lean code, the extension provides helpful suggestions:

```lean
def f : Nat := 5  -- Error: Unknown identifier 'Nat'
```
**Quick Fix Available:** → Add `import Std.Init.Data.Nat`

### Import Assistance
```lean
def f := List.map (+1) [1, 2, 3]  -- Error: Unknown identifier 'List'
```
**Quick Fix Available:** → Add `import Std.Data.List.Basic`

### Code Actions
- **Add missing parentheses** in function definitions
- **Add type annotations** when inference fails
- **Organize imports** automatically
- **Extract repeated expressions** into definitions
- **Convert between equivalent syntaxes**

### Formatting
The extension automatically formats your code according to Lean conventions:
```lean
-- Before
def   test(x:Nat):Nat:=x+1

-- After (formatted)
def test (x : Nat) : Nat := x + 1
```

## Troubleshooting

### Language Server Not Starting
1. **Check lean-analyzer installation**:
   ```bash
   lean-analyzer --version
   ```
2. **Set custom path** in settings if lean-analyzer is not in PATH:
   ```json
   {
     "leanAnalyzer.serverPath": "/path/to/lean-analyzer"
   }
   ```
3. **Check the output panel**: `View` → `Output` → Select "Lean Analyzer"

### No Syntax Highlighting
1. **Check file extension**: Make sure your file has `.lean` extension
2. **Check language mode**: Click on the language indicator in the status bar and select "Lean 4"

### Performance Issues
1. **Large files**: The extension handles large files well, but very large files (>10,000 lines) may be slower
2. **Memory usage**: Restart the language server if memory usage becomes high: `Ctrl+Shift+P` → "Lean Analyzer: Restart"

## Contributing

We welcome contributions! The extension is part of the [lean-claude](https://github.com/xiyuzhai/lean-claude) project.

### Development Setup
1. Clone the repository
2. Install dependencies: `npm install`
3. Open in VS Code: `code .`
4. Press `F5` to launch a new Extension Development Host

### Building
```bash
npm run compile    # Compile TypeScript
npm run watch      # Watch for changes
npm run package    # Create VSIX package
```

## License

MIT License - see [LICENSE](LICENSE) for details.

## Changelog

### 0.1.0
- Initial release
- Basic language server integration
- Enhanced error messages
- Code actions and quick fixes
- Syntax highlighting and snippets
- Import suggestions
- Document formatting

## Support

- **Issues**: [GitHub Issues](https://github.com/xiyuzhai/lean-claude/issues)
- **Discussions**: [GitHub Discussions](https://github.com/xiyuzhai/lean-claude/discussions)
- **Documentation**: [Project Wiki](https://github.com/xiyuzhai/lean-claude/wiki)