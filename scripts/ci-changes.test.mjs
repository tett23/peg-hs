import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';
import { needsBuild } from './ci-changes.mjs';

const root = dirname(dirname(fileURLToPath(import.meta.url)));
const script = join(root, 'scripts', 'ci-changes.mjs');
const zeros = '0'.repeat(40);

const run = (args, options = {}) =>
  spawnSync(process.execPath, [script, ...args], { encoding: 'utf8', ...options });

test('ADR 0101 I1: no paths do not need a build', () => {
  assert.equal(needsBuild([]), false);
});

test('ADR 0101 I1: documents that no build or test reads do not need a build', () => {
  for (const paths of [
    ['docs/adr/0101-run-ci-for-documents-that-tests-read.md'],
    ['docs/specifications.md', 'CONTRIBUTING.md'],
    ['docs/benchmarks/2026-11-01-lsp.md', 'docs/benchmarks/2026-11-01-lsp.svg'],
    ['docs/audits/2026-11-07-security.md'],
    ['conformance/README.md'],
    ['conformance/commonmark/tabs/sub/a.md'],
    ['packages/peg-grammar/sub/CHANGELOG.md'],
    ['packages/x/README.md'],
    ['docs/X.MD'],
  ]) assert.equal(needsBuild(paths), false, paths.join(' '));
});

test('ADR 0101 I1: each input in the list needs a build', () => {
  for (const path of [
    'docs/syntax.md',
    'docs/syntax.en.md',
    'README.md',
    'README.ja.md',
    'editors/README.md',
    'conformance/commonmark/tabs/item-quote.md',
    'docs/audits/2026-11-07-inj-module.hpeg.txt',
    'packages/peg-grammar/CHANGELOG.md',
  ]) assert.equal(needsBuild([path]), true, path);
});

test('ADR 0101 I1: a path that is not a document needs a build', () => {
  for (const paths of [
    ['conformance/commonmark/tabs/item-quote.html'],
    ['packages/peg-grammar/docs/x.txt'],
    ['docs/adr/0101-run-ci-for-documents-that-tests-read.md', 'packages/peg-grammar/src/Peg/Grammar.hs'],
    ['.github/workflows/ci.yml'],
  ]) assert.equal(needsBuild(paths), true, paths.join(' '));
});

test('ADR 0101 I2: the first push of a branch prints true without running git', () => {
  const result = run([zeros, 'HEAD'], { cwd: root, env: { PATH: '' } });
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout, 'true\n');
});

test('ADR 0101 I2: a commit that does not exist fails and prints nothing', () => {
  const result = run(['0'.repeat(39), 'HEAD'], { cwd: root });
  assert.notEqual(result.status, 0);
  assert.equal(result.stdout, '');
});

test('ADR 0101 I2: wrong arguments fail and print nothing', () => {
  for (const args of [[], ['HEAD'], ['', 'HEAD'], ['HEAD', ''], ['HEAD', 'HEAD', 'HEAD']]) {
    const result = run(args, { cwd: root });
    assert.notEqual(result.status, 0, JSON.stringify(args));
    assert.equal(result.stdout, '', JSON.stringify(args));
  }
});

test('ADR 0101 I3: a rename passes both of its paths to needsBuild', t => {
  const dir = mkdtempSync(join(tmpdir(), 'ci-changes-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const git = (...args) =>
    execFileSync('git', ['-c', 'user.name=t', '-c', 'user.email=t@example.com', ...args],
      { cwd: dir, encoding: 'utf8' }).trim();
  git('init', '-q');
  mkdirSync(join(dir, 'src'));
  mkdirSync(join(dir, 'docs'));
  const content = 'a line that stays the same\n'.repeat(20);
  for (const path of ['src/A.hs', 'docs/syntax.md'])
    writeFileSync(join(dir, path), `${path}\n${content}`);
  git('add', '-A');
  git('commit', '-q', '-m', 'first');
  const rename = (from, to) => {
    const before = git('rev-parse', 'HEAD');
    git('mv', from, to);
    git('commit', '-q', '-m', `move ${from}`);
    const result = run([before, git('rev-parse', 'HEAD')], { cwd: dir });
    assert.equal(result.status, 0, result.stderr);
    return result.stdout;
  };
  assert.equal(rename('src/A.hs', 'docs/A.md'), 'true\n');
  assert.equal(rename('docs/syntax.md', 'docs/old.md'), 'true\n');
  assert.equal(rename('docs/old.md', 'docs/new.md'), 'false\n');
});

test('ADR 0101 I4: ci.yml decides with ci-changes.mjs and has no paths-ignore', () => {
  const workflow = readFileSync(join(root, '.github', 'workflows', 'ci.yml'), 'utf8');
  assert.equal(workflow.includes('paths-ignore'), false);
  const start = workflow.indexOf('\n  changes:\n');
  assert.notEqual(start, -1);
  const rest = workflow.slice(start + 1);
  const next = rest.slice(1).search(/^ {2}[A-Za-z0-9_-]+:\n/m);
  const job = next === -1 ? rest : rest.slice(0, next + 1);
  assert.equal(job.split('scripts/ci-changes.mjs').length - 1, 2);
  assert.equal(/git diff/.test(job), false);
});
