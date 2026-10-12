// The scopes of the TextMate grammar (ADR 0034).
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';
import { textmateRanges } from './ranges.js';
import { tokenize } from './textmate.js';

const here = dirname(fileURLToPath(import.meta.url));

test('the scopes of every token of the table (golden; UPDATE=1 rewrites it)', () => {
  const lines = tokenize(readFileSync(join(here, 'sample.txt'), 'utf8')).map(
    (t) => `${t.line}:${t.start}-${t.end} ${JSON.stringify(t.text)} ${t.scopes.slice(1).join(' ')}`.trimEnd(),
  );
  const actual = lines.join('\n') + '\n';
  const golden = join(here, 'textmate.golden.txt');
  if (process.env.UPDATE) writeFileSync(golden, actual);
  assert.equal(actual, readFileSync(golden, 'utf8'));
});

test('an action ends at its brace, past braces in strings and nested braces', () => {
  const src = 'A <- B { "}" } C { f {x = 1} } D { \'}\' } E\n';
  assert.deepEqual(
    textmateRanges(src).filter((r) => r.startsWith('action')),
    ['action 1:8-1:15', 'action 1:18-1:31', 'action 1:34-1:41'],
  );
});

test('a multi-line action is one range', () => {
  assert.deepEqual(
    textmateRanges('A <- B {\n  x\n  } C\n').filter((r) => r.startsWith('action')),
    ['action 1:8-3:4'],
  );
});

test('the VS Code extension has the TextMate grammar', () => {
  assert.equal(
    readFileSync(join(here, '../vscode/syntaxes/peg.tmLanguage.json'), 'utf8'),
    readFileSync(join(here, '../textmate/peg.tmLanguage.json'), 'utf8'),
  );
});
