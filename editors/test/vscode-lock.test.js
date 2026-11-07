// The VS Code extension resolves minimatch to a version without the DoS of
// GHSA-g3hv-75wg-m249, by the override in its package.json (ADR 0077).
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '../..');

const lock = JSON.parse(readFileSync(join(root, 'editors/vscode/package-lock.json'), 'utf8'));

// Whether a version x.y.z is at least another.
const atLeast = (version, least) => {
  const [a, b] = [version, least].map((v) => v.split(/[.+-]/).slice(0, 3).map(Number));
  const i = a.findIndex((n, k) => n !== b[k]);
  return i === -1 || a[i] > b[i];
};

test('the lock resolves minimatch to 11.0.1 or later', () => {
  const versions = Object.entries(lock.packages)
    .filter(([path]) => path === 'node_modules/minimatch' || path.endsWith('/node_modules/minimatch'))
    .map(([, p]) => p.version);
  assert.ok(versions.length > 0, 'minimatch is in the lock');
  for (const v of versions) {
    assert.ok(atLeast(v, '11.0.1'), `minimatch ${v}`);
  }
});

test('the version comparison', () => {
  assert.deepEqual(
    ['11.0.1', '11.0.0', '10.2.6', '12.0.0', '11.1.0', '9.99.99'].map((v) => atLeast(v, '11.0.1')),
    [true, false, false, true, true, false],
  );
});
