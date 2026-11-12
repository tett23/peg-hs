import { execFileSync } from 'node:child_process';

// These paths either build peg-bench, supply its input, select its toolchain,
// or control the monitor. Documentation and test fixtures do not do so.
export function shouldMeasure(paths) {
  return paths.some(path =>
    (path.startsWith('conformance/') && !path.startsWith('conformance/test/') &&
      path !== 'conformance/README.md') ||
    /^packages\/[^/]+\/(src|grammar)\//.test(path) ||
    /^packages\/[^/]+\/[^/]+\.cabal$/.test(path) ||
    path === 'cabal.project' || path === 'cabal.project.freeze' ||
    path === '.github/workflows/lsp-latency.yml' ||
    path === 'scripts/lsp-latency.mjs' ||
    /^scripts\/lsp-(median|monitor-changes)(?:-issue)?(?:\.test)?\.mjs$/.test(path));
}

export function splitPaths(output) {
  return output.split('\0').filter(Boolean);
}

if (import.meta.main) {
  const [base, head] = process.argv.slice(2);
  if (!base || !head) throw new Error('Pass the before and head commits');
  const initial = /^0{40}$/.test(base);
  const args = initial
    ? ['ls-tree', '-r', '--name-only', '-z', head]
    : ['diff', '--no-renames', '--name-only', '-z', base, head, '--'];
  const paths = splitPaths(execFileSync('git', args, { encoding: 'utf8' }));
  console.log(shouldMeasure(paths) ? 'true' : 'false');
}
