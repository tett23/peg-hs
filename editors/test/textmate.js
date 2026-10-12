// Tokenizing with the TextMate grammar through vscode-textmate (ADR 0034).
import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import oniguruma from 'vscode-oniguruma';
import textmate from 'vscode-textmate';

const here = dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);

const wasm = readFileSync(join(dirname(require.resolve('vscode-oniguruma')), 'onig.wasm'));
await oniguruma.loadWASM(wasm.buffer.slice(wasm.byteOffset, wasm.byteOffset + wasm.byteLength));

const registry = new textmate.Registry({
  onigLib: Promise.resolve({
    createOnigScanner: (patterns) => new oniguruma.OnigScanner(patterns),
    createOnigString: (s) => new oniguruma.OnigString(s),
  }),
  // Haskell is embedded by its scope name; the tests do not load it.
  loadGrammar: async (scopeName) =>
    scopeName === 'source.peg'
      ? textmate.parseRawGrammar(readFileSync(join(here, '../textmate/peg.tmLanguage.json'), 'utf8'), 'peg.tmLanguage.json')
      : null,
});

const grammar = await registry.loadGrammar('source.peg');

/**
 * The tokens of a text: for each line (from 1), the tokens with their
 * columns in code points (from 1, the end just after) and scopes.
 * @param {string} text
 */
export function tokenize(text) {
  const lines = text.split('\n');
  if (lines.at(-1) === '') lines.pop();
  let stack = textmate.INITIAL;
  const out = [];
  lines.forEach((line, i) => {
    const r = grammar.tokenizeLine(line, stack);
    stack = r.ruleStack;
    for (const t of r.tokens) {
      const end = Math.min(t.endIndex, line.length);
      if (end <= t.startIndex) continue;
      out.push({
        line: i + 1,
        start: codePoints(line.slice(0, t.startIndex)) + 1,
        end: codePoints(line.slice(0, end)) + 1,
        text: line.slice(t.startIndex, end),
        scopes: t.scopes,
      });
    }
  });
  return out;
}

/** @param {string} s */
export function codePoints(s) {
  return [...s].length;
}
