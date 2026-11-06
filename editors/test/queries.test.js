// The queries of the tree-sitter grammar name only nodes of the grammar, and
// capture what they are for (ADR 0069).
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { isAbsolute, join } from 'node:path';
import { after, test } from 'node:test';
import { root } from './ranges.js';

const grammar = join(root, 'editors/tree-sitter-hpeg');
const bin = join(root, 'editors/node_modules/.bin/tree-sitter');

// The parser is built once; the queries run on it without rebuilding.
const build = mkdtempSync(join(tmpdir(), 'hpeg-queries-'));
const lib = join(build, 'hpeg.so');
execFileSync(bin, ['build', '-o', lib, '.'], { cwd: grammar, stdio: 'ignore' });
after(() => rmSync(build, { recursive: true }));

/**
 * The captures of a query on a file, with their rows from 0. The CLI fails on
 * a query that does not compile, as on a node or field the grammar lacks.
 * @param {string} query the file name in queries/
 * @param {string} file an absolute path, or a path relative to the repository
 */
function captures(query, file) {
  const output = execFileSync(
    bin,
    ['query', '-l', lib, '--lang-name', 'hpeg', '-c', join(grammar, 'queries', query), isAbsolute(file) ? file : join(root, file)],
    { cwd: grammar, encoding: 'utf8', maxBuffer: 1 << 28, stdio: ['ignore', 'pipe', 'pipe'] },
  );
  return [...output.matchAll(/capture: (?:\d+ - )?([\w.]+), start: \((\d+), \d+\), end: \((\d+), \d+\)(?:, text: `([^`]*)`)?/g)].map((m) => ({
    name: m[1],
    startRow: Number(m[2]),
    endRow: Number(m[3]),
    text: m[4],
  }));
}

const sample = 'editors/tree-sitter-hpeg/test/highlight/notation.hpeg';

test('every query compiles against the grammar', () => {
  for (const q of ['highlights.scm', 'injections.scm', 'folds.scm', 'indents.scm', 'locals.scm']) {
    assert.doesNotThrow(() => captures(q, sample), q);
  }
});

// The spaces before the argument of a directive are a token of the external
// scanner: a token of spaces in the grammar took in the space before <-.
test('highlights: the tokens of a definition do not take in the spaces before them', () => {
  const operators = captures('highlights.scm', sample).filter((c) => c.name === 'keyword.operator');
  assert.ok(operators.length > 0);
  assert.deepEqual([...new Set(operators.map((c) => c.text))].sort(), ['::', '<-']);
});

test('folds: a rule with its annotation, a verbatim block and a multi-line action', () => {
  const dir = mkdtempSync(join(tmpdir(), 'hpeg-folds-'));
  const file = join(dir, 'Folds.hpeg');
  writeFileSync(file, "%module M\n%{\nf = 1\n}%\n\nA :: Int\nA <- 'a' {\n    f\n  }\n\nB <- 'b'\n   / 'c'\n");
  try {
    const folds = captures('folds.scm', file)
      .filter((c) => c.name === 'fold')
      .map((c) => `${c.startRow}-${c.endRow}`);
    // The annotation and the definition are two nodes of one capture.
    assert.deepEqual(folds.sort(), ['1-3', '5-5', '6-8', '6-8', '6-8', '10-11'].sort());
  } finally {
    rmSync(dir, { recursive: true });
  }
});

test('indents: the alternatives of a definition align with its <-', () => {
  const indents = captures('indents.scm', sample).map((c) => c.name);
  assert.ok(indents.includes('indent.align'));
  assert.ok(indents.includes('indent.auto'));
});

test('locals: rule definitions, references and bindings', () => {
  const locals = captures('locals.scm', sample);
  const named = (name) => locals.filter((c) => c.name === name).map((c) => c.text);
  assert.ok(named('local.definition.function').includes('Expr'));
  assert.ok(named('local.reference').includes('Term'));
  assert.ok(named('local.reference').includes('Skip'), 'a rule in a directive');
  assert.ok(named('local.definition.var').includes('l'));
});
