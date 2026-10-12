// The editor grammars find the same comments, literals, classes, actions,
// rule names and labels as the notation's own grammar (ADR 0034).
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { test } from 'node:test';
import { expectedRanges, root, textmateRanges, treeSitterRanges, treeSitterTrees } from './ranges.js';

const expected = expectedRanges();
const files = [...expected.keys()];
const sorted = (rs) => [...rs].sort();

test('the TextMate grammar agrees with the syntax tree', () => {
  for (const f of files) {
    const actual = textmateRanges(readFileSync(join(root, f), 'utf8'));
    assert.deepEqual(sorted(actual), sorted(expected.get(f)), f);
  }
});

test('the tree-sitter grammar agrees with the syntax tree', () => {
  const actual = treeSitterRanges(files);
  files.forEach((f, i) => assert.deepEqual(sorted(actual[i]), sorted(expected.get(f)), f));
});

test('the tree-sitter grammar parses every grammar without errors', () => {
  const trees = treeSitterTrees(files);
  assert.equal(trees.length, files.length);
  files.forEach((f, i) => assert.doesNotMatch(trees[i], /\((ERROR|MISSING)/, f));
});
