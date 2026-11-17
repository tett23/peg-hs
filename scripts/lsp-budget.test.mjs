import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { chmodSync, existsSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';

const script = join(import.meta.dirname, 'lsp-budget.sh');

test('ADR 0102 I5: a wrong operation stops before the build with exit code 2', t => {
  const dir = mkdtempSync(join(tmpdir(), 'peg-hs-budget-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  // A cabal that leaves a mark when the script calls it.
  const mark = join(dir, 'called');
  const cabal = join(dir, 'cabal');
  writeFileSync(cabal, `#!/bin/sh\ntouch '${mark}'\nexit 1\n`);
  chmodSync(cabal, 0o755);
  for (const args of [[], ['latency'], ['diagnostics', 'semantic-tokens']]) {
    const result = spawnSync('sh', [script, ...args], {
      encoding: 'utf8',
      env: { ...process.env, PATH: `${dir}:${process.env.PATH}`, CABAL: cabal },
    });
    assert.equal(result.status, 2, JSON.stringify(args));
    assert.equal(result.stdout, '', JSON.stringify(args));
    assert.equal(existsSync(mark), false, JSON.stringify(args));
  }
});
