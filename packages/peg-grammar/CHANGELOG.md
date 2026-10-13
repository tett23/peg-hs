# Changelog of peg-grammar

The format follows the release notes of peg-hs: each version lists what was
Added, Changed, Removed and Fixed, with the ADRs that decided it.

## 0.1.0.0

The first release. peg-grammar reads `.peg` grammars and checks them.

### Added

- The parser of the `.peg` notation, written in the notation itself
  ([ADR 0004](https://github.com/tett23/peg-hs/blob/main/docs/adr/0004-peg-notation.md),
  [ADR 0020](https://github.com/tett23/peg-hs/blob/main/docs/adr/0020-unicode-identifiers-self-hosted.md),
  [ADR 0027](https://github.com/tett23/peg-hs/blob/main/docs/adr/0027-switch-to-self-hosted-parser.md)).
- The syntax of semantic predicates, parameterized rules, the parse
  environment and column references
  ([ADR 0012](https://github.com/tett23/peg-hs/blob/main/docs/adr/0012-context-sensitive-extensions.md)), `%language`
  ([ADR 0016](https://github.com/tett23/peg-hs/blob/main/docs/adr/0016-language-extensions.md)), `%nomemo`
  ([ADR 0017](https://github.com/tett23/peg-hs/blob/main/docs/adr/0017-nomemo-implementation.md)), `%syntax`
  ([ADR 0019](https://github.com/tett23/peg-hs/blob/main/docs/adr/0019-lossless-syntax-tree.md)), labels and recovery rules
  ([ADR 0021](https://github.com/tett23/peg-hs/blob/main/docs/adr/0021-error-recovery.md)) and rule templates
  ([ADR 0031](https://github.com/tett23/peg-hs/blob/main/docs/adr/0031-rule-templates.md)).
- Static checks: undefined and unused rules, left recursion that cannot
  grow, the count of values of groups and actions
  ([ADR 0030](https://github.com/tett23/peg-hs/blob/main/docs/adr/0030-unit-values-are-not-counted.md)), and the safety of
  labels ([ADR 0028](https://github.com/tett23/peg-hs/blob/main/docs/adr/0028-label-safety-check.md),
  [ADR 0029](https://github.com/tett23/peg-hs/blob/main/docs/adr/0029-label-safety-implementation-deviations.md),
  [ADR 0038](https://github.com/tett23/peg-hs/blob/main/docs/adr/0038-label-check-precision-and-strip-labels-entries.md)).
- `Peg.Grammar.Format`, the formatter of grammars
  ([ADR 0032](https://github.com/tett23/peg-hs/blob/main/docs/adr/0032-grammar-formatter.md)).
- `Peg.Grammar.Lint`, the linter of grammars
  ([ADR 0033](https://github.com/tett23/peg-hs/blob/main/docs/adr/0033-grammar-linter.md)).
- `Peg.Grammar.Highlight` and `Peg.Grammar.Outline`, what editors and
  the language server know of a grammar
  ([ADR 0034](https://github.com/tett23/peg-hs/blob/main/docs/adr/0034-syntax-highlighting.md),
  [ADR 0035](https://github.com/tett23/peg-hs/blob/main/docs/adr/0035-language-server.md)).
