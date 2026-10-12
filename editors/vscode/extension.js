// Starts the language server `peg-hs lsp` for .peg files (ADR 0035).
const vscode = require('vscode');
const { LanguageClient } = require('vscode-languageclient/node');

let client;

function activate() {
  const command = vscode.workspace.getConfiguration('peg-hs').get('path', 'peg-hs');
  client = new LanguageClient(
    'peg-hs',
    'peg-hs',
    { command, args: ['lsp'] },
    { documentSelector: [{ language: 'peg' }] },
  );
  return client.start();
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
