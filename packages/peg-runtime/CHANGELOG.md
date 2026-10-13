# Changelog of peg-runtime

The format follows the release notes of peg-hs: each version lists what was
Added, Changed, Removed and Fixed, with the ADRs that decided it.

## 0.1.0.0

The first release. peg-runtime is the only dependency of the modules that
`peg-hs gen` generates.

### Added

- The types that generated parsers return: positions (`Pos`, `Span`),
  parse errors with the farthest failure and the set of expected tokens
  (`ParseError`, `Expected`, `renderParseError`), and the syntax errors
  that recovery collects (`SyntaxError`)
  ([ADR 0005](https://github.com/tett23/peg-hs/blob/main/docs/adr/0005-error-reporting.md),
  [ADR 0008](https://github.com/tett23/peg-hs/blob/main/docs/adr/0008-source-positions.md),
  [ADR 0014](https://github.com/tett23/peg-hs/blob/main/docs/adr/0014-generated-module-api.md)).
- `Peg.Runtime.Internal`, the machinery that generated modules use: the
  packrat memo table, bounded left recursion, semantic predicates, the parse
  environment and column references
  ([ADR 0001](https://github.com/tett23/peg-hs/blob/main/docs/adr/0001-bounded-left-recursion.md),
  [ADR 0006](https://github.com/tett23/peg-hs/blob/main/docs/adr/0006-memoization-control.md),
  [ADR 0012](https://github.com/tett23/peg-hs/blob/main/docs/adr/0012-context-sensitive-extensions.md),
  [ADR 0013](https://github.com/tett23/peg-hs/blob/main/docs/adr/0013-roadmap-toolchain-memo.md),
  [ADR 0017](https://github.com/tett23/peg-hs/blob/main/docs/adr/0017-nomemo-implementation.md),
  [ADR 0018](https://github.com/tett23/peg-hs/blob/main/docs/adr/0018-tab-partial-consumption.md),
  [ADR 0024](https://github.com/tett23/peg-hs/blob/main/docs/adr/0024-discard-seed-dependents-only.md)).
  It exists for generated modules; a change to it is a major change under
  the PVP.
- `Peg.Runtime.Syntax`, the lossless syntax tree of grammars with
  `%syntax` ([ADR 0019](https://github.com/tett23/peg-hs/blob/main/docs/adr/0019-lossless-syntax-tree.md)).
- Recovery from syntax errors with labelled failures, so that one parse
  reports several errors ([ADR 0021](https://github.com/tett23/peg-hs/blob/main/docs/adr/0021-error-recovery.md)).
