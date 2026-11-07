// The executable of the language server is set only in the user settings,
// and the extension declares its support of untrusted workspaces (ADR 0080,
// SEC-08).
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '../..');

const manifest = JSON.parse(readFileSync(join(root, 'editors/vscode/package.json'), 'utf8'));

test('peg-hs.path has the scope machine', () => {
  assert.equal(manifest.contributes.configuration.properties['peg-hs.path'].scope, 'machine');
});

test('untrusted workspaces are supported in a limited way, without peg-hs.path', () => {
  const untrusted = manifest.capabilities?.untrustedWorkspaces;
  assert.ok(untrusted, 'capabilities.untrustedWorkspaces');
  assert.equal(untrusted.supported, 'limited');
  assert.ok(untrusted.restrictedConfigurations.includes('peg-hs.path'));
  assert.equal(typeof untrusted.description, 'string');
});
