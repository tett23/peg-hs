# Changelog of peg-codegen

The format follows the release notes of peg-hs: each version lists what was
Added, Changed, Removed and Fixed, with the ADRs that decided it.

## 0.1.0.0

The first release. peg-codegen turns a checked grammar into a Haskell
module.

### Added

- The generator: a pure function from a grammar to the text of a module,
  which depends on peg-runtime only
  ([ADR 0002](https://github.com/tett23/peg-hs/blob/main/docs/adr/0002-standalone-code-generator.md),
  [ADR 0003](https://github.com/tett23/peg-hs/blob/main/docs/adr/0003-typed-semantic-actions.md),
  [ADR 0014](https://github.com/tett23/peg-hs/blob/main/docs/adr/0014-generated-module-api.md)).
- Generated modules compile without warnings, keep the names of the
  grammar apart from their own, and point the errors of GHC at the lines of
  the grammar ([ADR 0014](https://github.com/tett23/peg-hs/blob/main/docs/adr/0014-generated-module-api.md)).
- Positions with the implicit binding `_span`
  ([ADR 0008](https://github.com/tett23/peg-hs/blob/main/docs/adr/0008-source-positions.md)).
- Values that are not used are discarded in the generated code
  ([ADR 0026](https://github.com/tett23/peg-hs/blob/main/docs/adr/0026-discard-unused-values.md)).
- The lossless syntax tree for grammars with `%syntax`
  ([ADR 0019](https://github.com/tett23/peg-hs/blob/main/docs/adr/0019-lossless-syntax-tree.md)) and error recovery
  ([ADR 0021](https://github.com/tett23/peg-hs/blob/main/docs/adr/0021-error-recovery.md)).
- Generation without the labels of a grammar, to check that labels do not
  change the language ([ADR 0028](https://github.com/tett23/peg-hs/blob/main/docs/adr/0028-label-safety-check.md),
  [ADR 0038](https://github.com/tett23/peg-hs/blob/main/docs/adr/0038-label-check-precision-and-strip-labels-entries.md)).
- The header of a generated module names the versions of peg-runtime it
  needs ([ADR 0046](https://github.com/tett23/peg-hs/blob/main/docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)).
- Builds with GHC 9.10, 9.12 and 9.14
  ([ADR 0045](https://github.com/tett23/peg-hs/blob/main/docs/adr/0045-fixes-before-v0-1-0.md)).

### Fixed

Since v0.1.0-rc1:

- With `%syntax`, a rule name that starts with a letter without upper
  case (kanji, kana, `_`) gets `Rule'` before its type name, so the module
  compiles ([ADR 0053](https://github.com/tett23/peg-hs/blob/main/docs/adr/0053-type-names-of-rules-without-case.md)).
