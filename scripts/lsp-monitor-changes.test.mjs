import assert from 'node:assert/strict';
import test from 'node:test';
import { shouldMeasure, splitPaths } from './lsp-monitor-changes.mjs';

test('invariant 1: documentation and unrelated source do not trigger measurement', () => {
  assert.equal(shouldMeasure(['docs/adr/0099-open-an-issue-for-lsp-median-latency.md']), false);
  assert.equal(shouldMeasure(['README.md', 'CONTRIBUTING.md']), false);
  assert.equal(shouldMeasure(['conformance/README.md']), false);
  assert.equal(shouldMeasure(['packages/peg-lsp/test/Main.hs']), false);
  assert.equal(shouldMeasure(['conformance/test/JsonMain.hs']), false);
});

test('invariant 1: each benchmark input triggers measurement', () => {
  for (const path of [
    'conformance/bench-main/BenchMain.hs',
    'conformance/bench/Memo.hpeg',
    'conformance/bench/input.md',
    'conformance/bench/Conformance/Bench/PegCounted.hs',
    'conformance/commonmark/Conformance/CommonMark.hs',
    'conformance/data/commonmark-spec-0.31.2/spec.txt',
    'conformance/data/lua-5.5.1-tests/strings.lua',
    'conformance/json/Json.hpeg',
    'conformance/lua/Conformance/Lua/Parser.hs',
    'packages/peg-lsp/src/Peg/Lsp/Server.hs',
    'packages/peg-grammar/grammar/Peg.hpeg',
    'packages/peg-codegen/src/Peg/Codegen.hs',
    'packages/peg-runtime/peg-runtime.cabal',
    'conformance/peg-conformance.cabal',
    'cabal.project',
    'cabal.project.freeze',
    '.github/workflows/lsp-latency.yml',
    'scripts/lsp-median.mjs',
    'scripts/lsp-median-issue.mjs',
    'scripts/lsp-monitor-changes.mjs',
    'scripts/lsp-latency.mjs',
  ]) assert.equal(shouldMeasure([path]), true, path);
});

test('invariant 1: a relevant file in a mixed push triggers measurement', () => {
  assert.equal(shouldMeasure(['README.md', 'packages/peg-lsp/src/Peg/Lsp/Server.hs']), true);
});

test('invariant 1: NUL-separated git paths preserve spaces and newlines', () => {
  const names = splitPaths('docs/README.md\0conformance/bench/quoted\nname.hs\0');
  assert.deepEqual(names, ['docs/README.md', 'conformance/bench/quoted\nname.hs']);
  assert.equal(shouldMeasure(names), true);
});
