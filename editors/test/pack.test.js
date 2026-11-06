// scripts/pack-editors.sh copies the editor grammars that releases carry
// (ADR 0073): the listed files, unchanged, and a tree-sitter grammar that
// builds and reads every grammar of the repository.
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readdirSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, relative } from 'node:path';
import { after, test } from 'node:test';
import { expectedRanges, root } from './ranges.js';

const out = join(mkdtempSync(join(tmpdir(), 'peg-hs-editors-')), 'peg-hs-editors');
execFileSync(join(root, 'scripts/pack-editors.sh'), [out]);
after(() => rmSync(join(out, '..'), { recursive: true, force: true }));

const walk = (dir) =>
  readdirSync(dir, { withFileTypes: true }).flatMap((e) =>
    e.isDirectory() ? walk(join(dir, e.name)) : [relative(out, join(dir, e.name))],
  );
const expected = readFileSync(join(root, 'editors/test/pack.txt'), 'utf8').split('\n').filter((l) => l !== '');
const packed = walk(out).sort();

test('the archive has the listed files only', () => {
  assert.deepEqual(packed, [...expected].sort());
});

test('the files are copies of the sources', () => {
  const source = (f) => (f === 'LICENSE' ? 'LICENSE' : join('editors', f));
  for (const f of packed) {
    assert.ok(readFileSync(join(out, f)).equals(readFileSync(join(root, source(f)))), f);
  }
});

test('the copied tree-sitter grammar reads every grammar without errors', () => {
  const files = [...expectedRanges().keys()];
  const bin = join(root, 'editors/node_modules/.bin/tree-sitter');
  const output = execFileSync(bin, ['parse', '-p', '.', ...files.map((f) => join(root, f))], {
    cwd: join(out, 'tree-sitter-hpeg'),
    encoding: 'utf8',
    maxBuffer: 1 << 28,
    stdio: ['ignore', 'pipe', 'ignore'],
  });
  assert.doesNotMatch(output, /\((ERROR|MISSING)/);
});
