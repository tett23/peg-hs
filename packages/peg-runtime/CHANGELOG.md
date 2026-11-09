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
- Builds with GHC 9.10, 9.12 and 9.14
  ([ADR 0045](https://github.com/tett23/peg-hs/blob/main/docs/adr/0045-fixes-before-v0-1-0.md)).

Since v0.1.0-rc2:

- `concatSyntax` of `Peg.Runtime.Syntax` joins syntax trees of
  consecutive texts into the tree of their concatenation, sharing their
  green nodes
  ([ADR 0071](https://github.com/tett23/peg-hs/blob/main/docs/adr/0071-incremental-parsing-in-the-language-server.md)).

Since v0.1.0-rc6:

- `decodeInput :: ByteString -> Either Utf8Error Text` of `Peg.Runtime`
  turns UTF-8 bytes, such as those of a file, into the input of the entry
  points of a generated module. It removes a byte order mark at the start
  and returns the position of the first ill-formed sequence as a
  `Utf8Error`, counted as the positions of `ParseError` are.
  `renderUtf8Error` renders it as `line:column: invalid UTF-8`.
  peg-runtime now depends on bytestring and on text 2.0.2 or later
  ([ADR 0093](https://github.com/tett23/peg-hs/blob/main/docs/adr/0093-utf8-bytestring-input.md)).

### Changed

Since v0.1.0-rc2:

- Parsing is faster: the set of terminals expected at the farthest
  failure is merged only when a parse error or a recovered syntax error
  needs it, a failure before the farthest one is not recorded, and a
  literal is compared in place. The results and the errors are unchanged
  ([ADR 0070](https://github.com/tett23/peg-hs/blob/main/docs/adr/0070-faster-checks-in-the-language-server.md)).
