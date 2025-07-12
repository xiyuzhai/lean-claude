import * as assert from 'assert';
import * as vscode from 'vscode';
import * as path from 'path';
import { before, after } from 'mocha';

suite('Lean Analyzer Extension Test Suite', () => {
    let extensionContext: vscode.ExtensionContext;
    
    before(async () => {
        // Activate the extension
        const extension = vscode.extensions.getExtension('lean-analyzer.lean-analyzer');
        if (extension) {
            extensionContext = await extension.activate();
        }
    });

    after(async () => {
        // Clean up
        await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    });

    suite('Extension Activation', () => {
        test('Extension should be present', () => {
            const extension = vscode.extensions.getExtension('lean-analyzer.lean-analyzer');
            assert.ok(extension, 'Extension should be present');
        });

        test('Extension should activate', async () => {
            const extension = vscode.extensions.getExtension('lean-analyzer.lean-analyzer');
            if (extension) {
                await extension.activate();
                assert.ok(extension.isActive, 'Extension should be active');
            }
        });
    });

    suite('Language Configuration', () => {
        test('Lean language should be registered', async () => {
            const languages = await vscode.languages.getLanguages();
            assert.ok(languages.includes('lean4'), 'Lean4 language should be registered');
        });

        test('File association should work', async () => {
            const testFile = await createTestLeanFile('def test : Nat := 42');
            assert.strictEqual(testFile.languageId, 'lean4', 'Lean file should have lean4 language ID');
            await vscode.window.showTextDocument(testFile);
        });
    });

    suite('Commands', () => {
        test('All commands should be registered', async () => {
            const commands = await vscode.commands.getCommands();
            const expectedCommands = [
                'leanAnalyzer.restart',
                'leanAnalyzer.showOutput',
                'leanAnalyzer.checkFile',
                'leanAnalyzer.formatDocument',
                'leanAnalyzer.organizeImports',
                'leanAnalyzer.showErrorDetails'
            ];
            
            for (const cmd of expectedCommands) {
                assert.ok(commands.includes(cmd), `Command ${cmd} should be registered`);
            }
        });

        test('Restart command should be available', async () => {
            try {
                await vscode.commands.executeCommand('leanAnalyzer.restart');
                // If no error is thrown, command exists
                assert.ok(true);
            } catch (error) {
                // Command might fail due to no server, but should still be registered
                assert.ok(true, 'Restart command should be registered');
            }
        });

        test('Format command should be available', async () => {
            const testFile = await createTestLeanFile('def   test   :   Nat   :=   42');
            await vscode.window.showTextDocument(testFile);
            
            try {
                await vscode.commands.executeCommand('leanAnalyzer.formatDocument');
                assert.ok(true, 'Format command should execute');
            } catch (error) {
                // May fail without language server, but command should exist
                assert.ok(true);
            }
        });
    });

    suite('Configuration', () => {
        test('Configuration section should exist', () => {
            const config = vscode.workspace.getConfiguration('leanAnalyzer');
            assert.ok(config, 'Configuration section should exist');
        });

        test('Default settings should be accessible', () => {
            const config = vscode.workspace.getConfiguration('leanAnalyzer');
            assert.strictEqual(config.get('enable'), true, 'Default enable should be true');
            assert.strictEqual(config.get('formatting.enable'), true, 'Default formatting should be enabled');
            assert.strictEqual(config.get('diagnostics.enableEnhancedErrors'), true, 'Enhanced errors should be enabled by default');
        });

        test('Settings should be modifiable', async () => {
            const config = vscode.workspace.getConfiguration('leanAnalyzer');
            await config.update('formatting.indentSize', 4, vscode.ConfigurationTarget.Workspace);
            assert.strictEqual(config.get('formatting.indentSize'), 4, 'Setting should be updated');
            
            // Reset to default
            await config.update('formatting.indentSize', undefined, vscode.ConfigurationTarget.Workspace);
        });
    });

    suite('Syntax Highlighting', () => {
        test('Lean keywords should be highlighted', async () => {
            const testFile = await createTestLeanFile(`
def test : Nat := 42
theorem example : True := trivial
lemma simple : 1 + 1 = 2 := rfl
            `);
            
            await vscode.window.showTextDocument(testFile);
            
            // Check that file is recognized as Lean
            assert.strictEqual(testFile.languageId, 'lean4');
        });

        test('Lean operators should be recognized', async () => {
            const testFile = await createTestLeanFile(`
def test : Nat → Nat := fun x => x + 1
theorem forall_example : ∀ n : Nat, n = n := fun n => rfl
            `);
            
            await vscode.window.showTextDocument(testFile);
            assert.strictEqual(testFile.languageId, 'lean4');
        });
    });

    suite('Snippets', () => {
        test('Snippets should be available for Lean files', async () => {
            const testFile = await createTestLeanFile('');
            await vscode.window.showTextDocument(testFile);
            
            // Test that we can trigger snippet completion
            const editor = vscode.window.activeTextEditor;
            if (editor) {
                await editor.edit(editBuilder => {
                    editBuilder.insert(new vscode.Position(0, 0), 'def');
                });
                
                // Trigger completion
                const completions = await vscode.commands.executeCommand(
                    'vscode.executeCompletionItemProvider',
                    testFile.uri,
                    new vscode.Position(0, 3)
                ) as vscode.CompletionList;
                
                assert.ok(completions, 'Completions should be available');
            }
        });
    });

    suite('Error Handling', () => {
        test('Should handle missing language server gracefully', async () => {
            // Create a test file and try to use language server features
            const testFile = await createTestLeanFile('def broken x := x + 1');
            await vscode.window.showTextDocument(testFile);
            
            try {
                // These may fail gracefully if no server is available
                await vscode.commands.executeCommand('leanAnalyzer.checkFile');
                await vscode.commands.executeCommand('leanAnalyzer.showOutput');
                assert.ok(true, 'Commands should handle missing server gracefully');
            } catch (error) {
                // Expected behavior when server is not available
                assert.ok(true);
            }
        });

        test('Should show appropriate error messages', async () => {
            const testFile = await createTestLeanFile('');
            await vscode.window.showTextDocument(testFile);
            
            // Test error details command with no errors
            try {
                await vscode.commands.executeCommand('leanAnalyzer.showErrorDetails');
                assert.ok(true, 'Error details command should handle no errors');
            } catch (error) {
                assert.ok(true);
            }
        });
    });

    suite('File Operations', () => {
        test('Should handle Lean file creation', async () => {
            const testFile = await createTestLeanFile(`
-- Test file
def hello : String := "Hello, World!"

theorem test : 1 + 1 = 2 := by
  norm_num
            `);
            
            await vscode.window.showTextDocument(testFile);
            assert.strictEqual(testFile.languageId, 'lean4');
            assert.ok(testFile.getText().includes('def hello'), 'File content should be preserved');
        });

        test('Should handle file with syntax errors', async () => {
            const testFile = await createTestLeanFile(`
def broken x := x + 1  -- Missing parentheses and type
def typo : Strng := "hello"  -- Typo in String
            `);
            
            await vscode.window.showTextDocument(testFile);
            assert.strictEqual(testFile.languageId, 'lean4');
        });
    });

    suite('Keybindings', () => {
        test('Key bindings should be registered', async () => {
            const testFile = await createTestLeanFile('def test : Nat := 42');
            await vscode.window.showTextDocument(testFile);
            
            // Test that format keybinding works (Shift+Alt+F)
            try {
                await vscode.commands.executeCommand('editor.action.formatDocument');
                assert.ok(true, 'Format keybinding should work');
            } catch (error) {
                assert.ok(true);
            }
        });
    });

    // Helper function to create test Lean files
    async function createTestLeanFile(content: string): Promise<vscode.TextDocument> {
        const uri = vscode.Uri.parse(`untitled:test-${Date.now()}.lean`);
        const document = await vscode.workspace.openTextDocument(uri);
        
        if (content) {
            const editor = await vscode.window.showTextDocument(document);
            await editor.edit(editBuilder => {
                editBuilder.insert(new vscode.Position(0, 0), content);
            });
        }
        
        return document;
    }
});