// The ranges the editor grammars are compared on (ADR 0034).
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { codePoints, tokenize } from './textmate.js';

const here = dirname(fileURLToPath(import.meta.url));
export const root = join(here, '../..');

/**
 * The ranges of the notation's own grammar, written by the tests of
 * peg-grammar: file -> lines of "kind line:col-line:col".
 */
export function expectedRanges() {
  const files = new Map();
  let current = null;
  for (const line of readFileSync(join(here, 'ranges.txt'), 'utf8').split('\n')) {
    if (line.startsWith('== ')) {
      current = [];
      files.set(line.slice(3), current);
    } else if (line !== '') {
      current.push(line);
    }
  }
  return files;
}

const pos = (l, c) => `${l}:${c}`;

const textmateKinds = [
  ['comment', (s) => s.startsWith('comment.line.number-sign.peg')],
  ['literal', (s) => /^string\.quoted\.(single|double)\.peg$/.test(s)],
  ['class', (s) => s === 'string.regexp.class.peg'],
  ['action', (s) => s === 'meta.embedded.action.peg'],
  ['rule-name', (s) => s === 'entity.name.function.rule.peg'],
  ['label', (s) => s === 'entity.name.tag.label.peg'],
];

/**
 * The ranges of the TextMate grammar. Consecutive tokens of one kind make
 * one range; an action continues over lines.
 * @param {string} text
 */
export function textmateRanges(text) {
  const lineLengths = text.split('\n').map(codePoints);
  const out = [];
  for (const [kind, test] of textmateKinds) {
    let open = null;
    const close = () => {
      if (open) out.push({ kind, ...open });
      open = null;
    };
    for (const t of tokenize(text)) {
      // The outermost scope of the kind: a nested literal of a template
      // argument is still one range.
      const index = t.scopes.findIndex(test);
      if (index < 0) {
        close();
        continue;
      }
      const continues =
        open &&
        ((open.endLine === t.line && open.endCol === t.start) ||
          (kind === 'action' && open.endLine === t.line - 1 && open.endCol === lineLengths[open.endLine - 1] + 1 && t.start === 1));
      if (continues && !(kind !== 'action' && t.scopes[index] !== open.scope)) {
        open.endLine = t.line;
        open.endCol = t.end;
      } else {
        close();
        open = { startLine: t.line, startCol: t.start, endLine: t.line, endCol: t.end, scope: t.scopes[index] };
      }
    }
    close();
  }
  return out.map((r) => `${r.kind} ${pos(r.startLine, r.startCol)}-${pos(r.endLine, r.endCol)}`);
}

const treeSitterKinds = new Map([
  ['comment', 'comment'],
  ['literal', 'literal'],
  ['class', 'class'],
  ['action', 'action'],
  ['rule_name', 'rule-name'],
  ['label', 'label'],
]);

/**
 * The syntax trees the tree-sitter CLI prints for each file. Their columns
 * are in bytes.
 * @param {string[]} files paths relative to the repository
 */
export function treeSitterTrees(files) {
  const bin = join(root, 'editors/node_modules/.bin/tree-sitter');
  const output = execFileSync(bin, ['parse', '-p', '.', ...files.map((f) => join(root, f))], {
    cwd: join(root, 'editors/tree-sitter-peg'),
    encoding: 'utf8',
    maxBuffer: 1 << 28,
    stdio: ['ignore', 'pipe', 'ignore'],
  });
  return output.split(/^(?=\(source_file )/m).filter((t) => t.startsWith('(source_file'));
}

/**
 * The ranges of the tree-sitter grammar for each file.
 * @param {string[]} files paths relative to the repository
 */
export function treeSitterRanges(files) {
  const trees = treeSitterTrees(files);
  return files.map((f, i) => {
    const lines = readFileSync(join(root, f), 'utf8').split('\n');
    const col = (row, byte) => codePoints(Buffer.from(lines[row] ?? '', 'utf8').subarray(0, byte).toString('utf8')) + 1;
    const out = [];
    for (const m of trees[i].matchAll(/\((\w+) \[(\d+), (\d+)\] - \[(\d+), (\d+)\]/g)) {
      const kind = treeSitterKinds.get(m[1]);
      if (!kind) continue;
      const [sr, sc, er, ec] = [m[2], m[3], m[4], m[5]].map(Number);
      out.push(`${kind} ${pos(sr + 1, col(sr, sc))}-${pos(er + 1, col(er, ec))}`);
    }
    return out;
  });
}
