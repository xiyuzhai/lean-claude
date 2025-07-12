import * as vscode from 'vscode';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    TransportKind,
    RevealOutputChannelOn,
} from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: vscode.ExtensionContext) {
    console.log('Lean Analyzer extension is now active!');

    // Start the language server
    startLanguageServer(context);

    // Register commands
    registerCommands(context);

    // Register providers
    registerProviders(context);

    // Set up status bar
    setupStatusBar(context);
}

function startLanguageServer(context: vscode.ExtensionContext) {
    const config = vscode.workspace.getConfiguration('leanAnalyzer');
    
    if (!config.get('enable')) {
        return;
    }

    // Get server path from configuration or try to find in PATH
    let serverPath = config.get<string>('serverPath') || 'lean-analyzer';
    
    // Server options
    const serverOptions: ServerOptions = {
        run: { command: serverPath, transport: TransportKind.stdio },
        debug: { command: serverPath, transport: TransportKind.stdio }
    };

    // Client options
    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'lean4' }],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.lean')
        },
        revealOutputChannelOn: RevealOutputChannelOn.Info,
        initializationOptions: {
            formatting: {
                enable: config.get('formatting.enable'),
                indentSize: config.get('formatting.indentSize'),
                maxLineLength: config.get('formatting.maxLineLength')
            },
            codeActions: {
                enable: config.get('codeActions.enable')
            },
            diagnostics: {
                enableEnhancedErrors: config.get('diagnostics.enableEnhancedErrors')
            },
            completion: {
                enable: config.get('completion.enable')
            },
            hover: {
                enable: config.get('hover.enable')
            },
            inlayHints: {
                enable: config.get('inlayHints.enable')
            },
            importSuggestions: {
                enable: config.get('importSuggestions.enable')
            }
        }
    };

    // Create the language client
    client = new LanguageClient(
        'leanAnalyzer',
        'Lean Analyzer',
        serverOptions,
        clientOptions
    );

    // Start the client
    client.start().then(() => {
        console.log('Lean Analyzer language server started successfully');
        updateStatusBar('ready');
    }).catch(error => {
        console.error('Failed to start Lean Analyzer language server:', error);
        vscode.window.showErrorMessage(
            `Failed to start Lean Analyzer: ${error.message}. ` +
            'Please check that lean-analyzer is installed and accessible.'
        );
        updateStatusBar('error');
    });

    context.subscriptions.push(client);
}

function registerCommands(context: vscode.ExtensionContext) {
    // Restart command
    const restartCommand = vscode.commands.registerCommand('leanAnalyzer.restart', async () => {
        if (client) {
            await client.stop();
            updateStatusBar('restarting');
            setTimeout(() => {
                startLanguageServer(context);
            }, 1000);
        }
    });

    // Show output command
    const showOutputCommand = vscode.commands.registerCommand('leanAnalyzer.showOutput', () => {
        if (client) {
            client.outputChannel.show();
        }
    });

    // Check file command
    const checkFileCommand = vscode.commands.registerCommand('leanAnalyzer.checkFile', async () => {
        const editor = vscode.window.activeTextEditor;
        if (editor && editor.document.languageId === 'lean4') {
            await vscode.commands.executeCommand('vscode.executeDocumentDiagnostics', editor.document.uri);
            vscode.window.showInformationMessage('File checked for errors');
        }
    });

    // Format document command
    const formatDocumentCommand = vscode.commands.registerCommand('leanAnalyzer.formatDocument', async () => {
        const editor = vscode.window.activeTextEditor;
        if (editor && editor.document.languageId === 'lean4') {
            await vscode.commands.executeCommand('editor.action.formatDocument');
        }
    });

    // Organize imports command
    const organizeImportsCommand = vscode.commands.registerCommand('leanAnalyzer.organizeImports', async () => {
        const editor = vscode.window.activeTextEditor;
        if (editor && editor.document.languageId === 'lean4') {
            await vscode.commands.executeCommand('editor.action.organizeImports');
        }
    });

    // Show error details command
    const showErrorDetailsCommand = vscode.commands.registerCommand('leanAnalyzer.showErrorDetails', async () => {
        const editor = vscode.window.activeTextEditor;
        if (editor && editor.document.languageId === 'lean4') {
            const diagnostics = vscode.languages.getDiagnostics(editor.document.uri);
            if (diagnostics.length > 0) {
                const items = diagnostics.map(d => ({
                    label: d.message,
                    detail: `Line ${d.range.start.line + 1}: ${d.message}`,
                    diagnostic: d
                }));
                
                const selected = await vscode.window.showQuickPick(items, {
                    placeHolder: 'Select an error to see details'
                });
                
                if (selected) {
                    const position = selected.diagnostic.range.start;
                    editor.selection = new vscode.Selection(position, position);
                    editor.revealRange(selected.diagnostic.range);
                }
            } else {
                vscode.window.showInformationMessage('No errors found in current file');
            }
        }
    });

    context.subscriptions.push(
        restartCommand,
        showOutputCommand,
        checkFileCommand,
        formatDocumentCommand,
        organizeImportsCommand,
        showErrorDetailsCommand
    );
}

function registerProviders(context: vscode.ExtensionContext) {
    // Register hover provider for enhanced error information
    const hoverProvider = vscode.languages.registerHoverProvider('lean4', {
        provideHover(document, position) {
            const diagnostics = vscode.languages.getDiagnostics(document.uri);
            const hoveredDiagnostic = diagnostics.find(d => d.range.contains(position));
            
            if (hoveredDiagnostic) {
                const markdown = new vscode.MarkdownString();
                markdown.appendMarkdown(`**Error:** ${hoveredDiagnostic.message}\n\n`);
                
                // Add suggestions if available
                if (hoveredDiagnostic.code) {
                    markdown.appendMarkdown(`**Code:** ${hoveredDiagnostic.code}\n\n`);
                }
                
                // Add related information
                if (hoveredDiagnostic.relatedInformation) {
                    markdown.appendMarkdown('**Related Information:**\n');
                    hoveredDiagnostic.relatedInformation.forEach(info => {
                        markdown.appendMarkdown(`- ${info.message}\n`);
                    });
                }
                
                return new vscode.Hover(markdown);
            }
        }
    });

    // Register code lens provider for quick actions
    const codeLensProvider = vscode.languages.registerCodeLensProvider('lean4', {
        provideCodeLenses(document) {
            const codeLenses: vscode.CodeLens[] = [];
            const text = document.getText();
            const lines = text.split('\n');
            
            lines.forEach((line, index) => {
                // Add "Check Proof" lens for theorem lines
                if (line.trim().startsWith('theorem ') || line.trim().startsWith('lemma ')) {
                    const range = new vscode.Range(index, 0, index, line.length);
                    const lens = new vscode.CodeLens(range, {
                        title: '$(check) Check Proof',
                        command: 'leanAnalyzer.checkFile'
                    });
                    codeLenses.push(lens);
                }
                
                // Add "Format" lens for definition lines
                if (line.trim().startsWith('def ')) {
                    const range = new vscode.Range(index, 0, index, line.length);
                    const lens = new vscode.CodeLens(range, {
                        title: '$(symbol-ruler) Format',
                        command: 'leanAnalyzer.formatDocument'
                    });
                    codeLenses.push(lens);
                }
            });
            
            return codeLenses;
        }
    });

    context.subscriptions.push(hoverProvider, codeLensProvider);
}

let statusBarItem: vscode.StatusBarItem;

function setupStatusBar(context: vscode.ExtensionContext) {
    statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 100);
    statusBarItem.command = 'leanAnalyzer.showOutput';
    updateStatusBar('starting');
    statusBarItem.show();
    
    context.subscriptions.push(statusBarItem);
    
    // Update status when active editor changes
    vscode.window.onDidChangeActiveTextEditor(editor => {
        if (editor && editor.document.languageId === 'lean4') {
            statusBarItem.show();
        } else {
            statusBarItem.hide();
        }
    });
}

function updateStatusBar(status: 'starting' | 'ready' | 'error' | 'restarting') {
    if (!statusBarItem) {return;}
    
    switch (status) {
        case 'starting':
            statusBarItem.text = '$(loading~spin) Lean Analyzer: Starting...';
            statusBarItem.color = new vscode.ThemeColor('statusBarItem.prominentForeground');
            break;
        case 'ready':
            statusBarItem.text = '$(check) Lean Analyzer: Ready';
            statusBarItem.color = new vscode.ThemeColor('statusBarItem.foreground');
            break;
        case 'error':
            statusBarItem.text = '$(error) Lean Analyzer: Error';
            statusBarItem.color = new vscode.ThemeColor('statusBarItem.errorForeground');
            break;
        case 'restarting':
            statusBarItem.text = '$(loading~spin) Lean Analyzer: Restarting...';
            statusBarItem.color = new vscode.ThemeColor('statusBarItem.prominentForeground');
            break;
    }
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}