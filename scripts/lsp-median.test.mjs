import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { cases } from './lsp-latency.mjs';
import { summarize } from './lsp-median.mjs';

function inputs() {
  return ['Memo', 'Golem'].map(() => ['criterion', '1.6.5.0', cases.map(name => ({
    reportName: `lsp (712 lines)/${name}`,
    reportKeys: ['time', 'iters', 'allocated'],
    reportMeasured: [[0.032, 2, 0]],
  }))]);
}

test('invariant 1: all twelve cases require valid raw samples', () => {
  assert.equal(summarize(inputs()).length, 12);
  const changes = [
    rows => rows.pop(),
    rows => rows.push(structuredClone(rows[0])),
    rows => { rows[0].reportMeasured = []; },
    ...[0, -1, NaN, Infinity, null, '1'].map(value =>
      rows => { rows[0].reportMeasured[0][0] = value; }),
    ...[0, -1, 0.5, NaN, Infinity, null, '2'].map(value =>
      rows => { rows[0].reportMeasured[0][1] = value; }),
    rows => { rows[0].reportKeys = ['time', 'allocated']; },
    rows => { rows[0].reportKeys = ['time', 'time', 'iters']; },
  ];
  for (const change of changes) {
    for (const index of [0, 1]) {
      const reports = inputs();
      change(reports[index][2]);
      assert.throws(() => summarize(reports));
    }
  }
});

test('invariant 2: median uses time per iteration and compares unrounded seconds', () => {
  const reports = inputs();
  const [first, second, third] = reports[0][2];
  first.reportMeasured = [[0.015, 1, 0], [0.016, 1, 0], [0.040, 1, 0]];
  second.reportMeasured = [[0.015, 1, 0], [0.017002, 1, 0]];
  third.reportMeasured = [[0.032, 2, 0]];
  const rows = summarize(reports);
  assert.equal(rows[0].seconds, 0.016);
  assert.equal(rows[1].seconds, 0.016001);
  assert.equal(rows[2].seconds, 0.016);
  assert.deepEqual(rows.filter(row => row.seconds > 0.016), [rows[1]]);
});

test('invariant 1: named columns survive a changed Criterion column order', () => {
  const reports = inputs();
  reports[0][2][0].reportKeys = ['allocated', 'iters', 'time'];
  reports[0][2][0].reportMeasured = [[0, 2, 0.034]];
  assert.equal(summarize(reports)[0].seconds, 0.017);
});

test('invariant 2: averaging two finite high samples stays finite', () => {
  const reports = inputs();
  reports[0][2][0].reportMeasured = [[1e308, 1, 0], [1e308, 1, 0]];
  assert.equal(summarize(reports)[0].seconds, 1e308);
});

test('invariant 2: CLI prints twelve rows and writes every exceeded case', () => {
  const dir = mkdtempSync(join(tmpdir(), 'peg-hs-median-'));
  try {
    const reports = inputs();
    reports[0][2][0].reportMeasured = [[0.034, 2, 0]];
    reports[1][2][1].reportMeasured = [[0.018, 1, 0]];
    const files = ['Memo.json', 'Golem.json'].map((name, index) => {
      const file = join(dir, name);
      writeFileSync(file, JSON.stringify(reports[index]));
      return file;
    });
    const output = join(dir, 'github-output');
    const stdout = execFileSync(process.execPath, [join(import.meta.dirname, 'lsp-median.mjs'), ...files],
      { encoding: 'utf8', env: { ...process.env, GITHUB_OUTPUT: output } });
    assert.equal(stdout.split('\n').filter(line => line.startsWith('| Memo |') || line.startsWith('| Golem |')).length, 12);
    assert.deepEqual(JSON.parse(readFileSync(output, 'utf8').trim().replace(/^exceeded=/, '')), [
      { grammar: 'Memo', name: cases[0], seconds: 0.017 },
      { grammar: 'Golem', name: cases[1], seconds: 0.018 },
    ]);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});

test('invariant 1: invalid CLI input fails without writing a notification result', () => {
  const dir = mkdtempSync(join(tmpdir(), 'peg-hs-median-'));
  try {
    const reports = inputs();
    reports[0][2][0].reportMeasured = [];
    const files = ['Memo.json', 'Golem.json'].map((name, index) => {
      const file = join(dir, name);
      writeFileSync(file, JSON.stringify(reports[index]));
      return file;
    });
    const output = join(dir, 'github-output');
    const result = spawnSync(process.execPath, [join(import.meta.dirname, 'lsp-median.mjs'), ...files],
      { encoding: 'utf8', env: { ...process.env, GITHUB_OUTPUT: output } });
    assert.notEqual(result.status, 0);
    assert.throws(() => readFileSync(output, 'utf8'));
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
