import { execFileSync } from 'node:child_process';

// Whether a change needs the build and the tests (ADR 0101). A document is a
// path under the root docs/ or a path that ends with .md. The inputs are the
// documents that a build or a test reads; a change that makes a build or a
// test read another document adds it here, and a change that stops reading
// one removes it. A * matches one name without a /.
export const inputs = [
  'docs/syntax.md',
  'docs/syntax.en.md',
  'README.md',
  'README.ja.md',
  'editors/README.md',
  'conformance/commonmark/tabs/*.md',
  'docs/audits/2026-11-07-inj-module.hpeg.txt',
  'packages/*/CHANGELOG.md',
  'docs/budgets.md',
];

const escape = text => text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
const patterns = inputs.map(input =>
  new RegExp(`^${input.split('*').map(escape).join('[^/]+')}$`));

const isDocument = path => path.startsWith('docs/') || path.endsWith('.md');
const isInput = path => patterns.some(pattern => pattern.test(path));

export function needsBuild(paths) {
  return paths.some(path => !isDocument(path) || isInput(path));
}

const fail = message => {
  console.error(message);
  process.exitCode = 1;
};

if (import.meta.main) {
  const args = process.argv.slice(2);
  if (args.length !== 2 || args.some(arg => arg === '')) {
    fail('Usage: node scripts/ci-changes.mjs <before> <after>');
  } else if (/^0{40}$/.test(args[0])) {
    // The first push of a branch has no commit before it.
    console.log('true');
  } else {
    try {
      const output = execFileSync(
        'git', ['diff', '--no-renames', '--name-only', '-z', args[0], args[1], '--'],
        { encoding: 'utf8', stdio: ['ignore', 'pipe', 'inherit'] });
      console.log(needsBuild(output.split('\0').filter(Boolean)) ? 'true' : 'false');
    } catch (error) {
      fail(`git diff failed: ${error.message}`);
    }
  }
}
