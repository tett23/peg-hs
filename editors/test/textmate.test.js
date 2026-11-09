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
    readFileSync(join(here, '../vscode/syntaxes/hpeg.tmLanguage.json'), 'utf8'),
    readFileSync(join(here, '../textmate/hpeg.tmLanguage.json'), 'utf8'),
  );
});

// The language is hpeg, for files with the extension .hpeg (ADR 0050).
test('the VS Code extension takes .hpeg files as the language hpeg', () => {
  const manifest = JSON.parse(readFileSync(join(here, '../vscode/package.json'), 'utf8'));
  const [language] = manifest.contributes.languages;
  assert.equal(language.id, 'hpeg');
  assert.deepEqual(language.extensions, ['.hpeg']);
  assert.deepEqual(manifest.contributes.grammars.map((g) => [g.language, g.scopeName]), [['hpeg', 'source.hpeg']]);
  assert.ok(manifest.activationEvents.includes('onLanguage:hpeg'));
});

// Grammars are formatted on save by default (ADR 0069).
test('the VS Code extension formats grammars on save by default', () => {
  const manifest = JSON.parse(readFileSync(join(here, '../vscode/package.json'), 'utf8'));
  assert.deepEqual(manifest.contributes.configurationDefaults, { '[hpeg]': { 'editor.formatOnSave': true } });
});

test('the path of %import has its own scope, and %library is a directive (ADR 0092)', () => {
  const scopesOf = (src) => tokenize(src).map((t) => [t.text, t.scopes.at(-1)]).filter(([, s]) => s !== 'source.hpeg');
  assert.deepEqual(scopesOf('%library # l\n%import lex/Ident.hpeg # i\n'), [
    ['%library', 'keyword.other.directive.hpeg'],
    ['# l', 'comment.line.number-sign.hpeg'],
    ['%import', 'keyword.other.directive.hpeg'],
    ['lex/Ident.hpeg', 'string.other.path.hpeg'],
    ['# i', 'comment.line.number-sign.hpeg'],
  ]);
});

test('the arguments of directives have their own scopes (ADR 0069)', () => {
  const scopesOf = (src) => tokenize(src).map((t) => [t.text, t.scopes.at(-1)]);
  assert.deepEqual(scopesOf('%module A.B # c\n'), [
    ['%module', 'keyword.other.directive.hpeg'],
    [' ', 'source.hpeg'],
    ['A.B', 'entity.name.namespace.hpeg'],
    [' ', 'source.hpeg'],
    ['# c', 'comment.line.number-sign.hpeg'],
  ]);
  assert.deepEqual(scopesOf('%recover l R\n%start S\n%safe m\n').filter(([, s]) => s !== 'source.hpeg'), [
    ['%recover', 'keyword.other.directive.hpeg'],
    ['l', 'entity.name.tag.label.directive.hpeg'],
    ['R', 'variable.other.rule.directive.hpeg'],
    ['%start', 'keyword.other.directive.hpeg'],
    ['S', 'variable.other.rule.directive.hpeg'],
    ['%safe', 'keyword.other.directive.hpeg'],
    ['m', 'entity.name.tag.label.directive.hpeg'],
  ]);
  assert.deepEqual(scopesOf('%language A, B\n').filter(([, s]) => s !== 'source.hpeg'), [
    ['%language', 'keyword.other.directive.hpeg'],
    ['A', 'constant.language.extension.hpeg'],
    [',', 'punctuation.separator.comma.hpeg'],
    ['B', 'constant.language.extension.hpeg'],
  ]);
});

test('constructor names and the classes of %deriving have the scopes of Haskell (ADR 0075)', () => {
  const scopesOf = (src) => tokenize(src).map((t) => [t.text, t.scopes.at(-1)]);
  assert.deepEqual(scopesOf('%deriving Eq, GHC.Generics.Generic # c\n').filter(([, s]) => s !== 'source.hpeg'), [
    ['%deriving', 'keyword.other.directive.hpeg'],
    ['Eq', 'storage.type.class.hpeg'],
    [',', 'punctuation.separator.comma.hpeg'],
    ['GHC.Generics.Generic', 'storage.type.class.hpeg'],
    ['# c', 'comment.line.number-sign.hpeg'],
  ]);
  assert.deepEqual(scopesOf("A <- B C @Pair\n").filter(([t]) => t === '@' || t === 'Pair'), [
    ['@', 'punctuation.definition.constructor.hpeg'],
    ['Pair', 'constant.other.constructor.hpeg'],
  ]);
});
