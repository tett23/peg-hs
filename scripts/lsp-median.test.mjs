import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { cases, limitSeconds, summarize } from './lsp-median.mjs';

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

// Runs lsp-median.mjs with the options and the reports, each written to a
// file, in a directory of its own.
function cli(options, reports) {
  const dir = mkdtempSync(join(tmpdir(), 'peg-hs-median-'));
  try {
    const files = reports.map((report, index) => {
      const file = join(dir, `${index}.json`);
      writeFileSync(file, JSON.stringify(report));
      return file;
    });
    const { GITHUB_OUTPUT, ...env } = process.env;
    return spawnSync(process.execPath, [join(import.meta.dirname, 'lsp-median.mjs'), ...options, ...files],
      { encoding: 'utf8', env });
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const sampleOf = (reports, grammar, name) =>
  reports[grammar][2].find(report => report.reportName.endsWith(`/${name}`));
const diagnostics = cases.filter(name => name.endsWith('range: decode, check, encode'));
const semanticTokens = cases.filter(name => name.endsWith('range, and the semantic tokens'));

test('ADR 0102 I1: the judgment fails on a missing case, empty samples or zero iterations', () => {
  for (const index of [0, 1]) {
    for (const change of [
      rows => rows.pop(),
      rows => { rows[0].reportMeasured = []; },
      rows => { rows[0].reportMeasured[0][1] = 0; },
    ]) {
      const reports = inputs();
      change(reports[index][2]);
      assert.notEqual(cli(['--fail-on-exceed'], reports).status, 0);
    }
  }
});

test('ADR 0102 I1: the judgment fails on a duplicate case', () => {
  const reports = inputs();
  reports[1][2].push(structuredClone(reports[1][2][0]));
  assert.notEqual(cli(['--fail-on-exceed'], reports).status, 0);
});

test('ADR 0102 I2: a largest median of exactly 16 ms passes', () => {
  const reports = inputs();
  for (const grammar of [0, 1]) for (const report of reports[grammar][2]) report.reportMeasured = [[0.016, 1, 0]];
  const result = cli(['--fail-on-exceed'], reports);
  assert.equal(result.status, 0, result.stderr);
});

test('ADR 0102 I2: one median of 16.001 ms fails', () => {
  const reports = inputs();
  sampleOf(reports, 1, cases[5]).reportMeasured = [[0.016001, 1, 0]];
  const result = cli(['--fail-on-exceed'], reports);
  assert.equal(result.status, 1);
  assert.match(result.stdout, /^\| Golem \| .* \| yes \|$/m);
});

test('ADR 0102 I2: samples of 15 ms and 17.002 ms have a median of 16.001 ms and fail', () => {
  const reports = inputs();
  sampleOf(reports, 0, cases[2]).reportMeasured = [[0.015, 1, 0], [0.017002, 1, 0]];
  const result = cli(['--fail-on-exceed'], reports);
  assert.equal(result.status, 1);
  assert.match(result.stdout, /^\| Memo \| .* \| yes \|$/m);
});

test('ADR 0102 I2: one sample of 0.032 seconds over two iterations is 16 ms and passes', () => {
  const reports = inputs();
  sampleOf(reports, 1, cases[0]).reportMeasured = [[0.032, 2, 0]];
  const result = cli(['--fail-on-exceed'], reports);
  assert.equal(result.status, 0, result.stderr);
});

test('ADR 0102 I3: the judgment reads only the head reports', () => {
  const base = inputs();
  sampleOf(base, 0, cases[0]).reportMeasured = [[0.040, 1, 0]];
  const head = inputs();
  assert.equal(cli(['--fail-on-exceed'], head).status, 0);
  assert.notEqual(cli(['--fail-on-exceed'], [...base, ...head]).status, 0);
  assert.notEqual(cli(['--fail-on-exceed'], [head[0]]).status, 0);
});

test('ADR 0102 I6: the largest median of the semantic tokens is the last line in ms', () => {
  const reports = inputs();
  const values = [0.0092, 0.0095, 0.0096, 0.0100, 0.0099, 0.0102];
  semanticTokens.flatMap(name => [[0, name], [1, name]]).forEach(([grammar, name], index) => {
    sampleOf(reports, grammar, name).reportMeasured = [[values[index], 1, 0]];
  });
  const result = cli(['--max', 'semantic-tokens'], reports);
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout.trimEnd().split('\n').at(-1), '10.200');
});

test('ADR 0102 I6: a largest median over the budget still prints and succeeds', () => {
  const reports = inputs();
  sampleOf(reports, 1, diagnostics[1]).reportMeasured = [[0.020, 1, 0]];
  const result = cli(['--max', 'diagnostics'], reports);
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout.trimEnd().split('\n').at(-1), '20.000');
});

test('ADR 0102 I6: a missing case fails and prints no number', () => {
  const reports = inputs();
  reports[0][2] = reports[0][2].filter(report => !report.reportName.endsWith(`/${diagnostics[2]}`));
  const result = cli(['--max', 'diagnostics'], reports);
  assert.notEqual(result.status, 0);
  assert.equal(result.stdout, '');
});

test('ADR 0102 I6: an unknown operation fails and prints no number', () => {
  const result = cli(['--max', 'latency'], inputs());
  assert.notEqual(result.status, 0);
  assert.equal(result.stdout, '');
});

test('ADR 0102 I7: the two budgets of docs/budgets.md equal the limit in ms', () => {
  const budgets = readFileSync(join(import.meta.dirname, '..', 'docs', 'budgets.md'), 'utf8');
  const rows = budgets.split('\n')
    .filter(line => line.startsWith('|') && line.includes('ADR 0102 A3'))
    .map(line => line.split('|').slice(1, -1).map(cell => cell.trim()));
  assert.deepEqual(rows.map(row => row[4]),
    ['`scripts/lsp-budget.sh diagnostics`', '`scripts/lsp-budget.sh semantic-tokens`']);
  for (const row of rows) {
    assert.equal(row[2], '`<=`');
    assert.equal(Number(row[3]), limitSeconds * 1000);
  }
});
