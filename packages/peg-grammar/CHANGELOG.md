# Changelog of peg-grammar

The format follows the release notes of peg-hs: each version lists what was
Added, Changed, Removed and Fixed, with the ADRs that decided it.

## 0.1.0.0

The first release. peg-grammar reads `.hpeg` grammars and checks them.

### Added

- The parser of the `.hpeg` notation, written in the notation itself
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
- Builds with GHC 9.10, 9.12 and 9.14
  ([ADR 0045](https://github.com/tett23/peg-hs/blob/main/docs/adr/0045-fixes-before-v0-1-0.md)).

Since v0.1.0-rc1:

- The arguments of a template may use the parameters of the rule that
  calls it, as `Lines<Item(ind)>` in `B(ind :: Int)`. The instance takes
  those parameters, and an argument that uses a binding of the caller is
  an error ([ADR 0055](https://github.com/tett23/peg-hs/blob/main/docs/adr/0055-templates-and-parameterized-rules-in-stages.md)).

### Changed

Since v0.1.0-rc1:

- The notation is called the `.hpeg` notation, after the extension of its
  files ([ADR 0050](https://github.com/tett23/peg-hs/blob/main/docs/adr/0050-hpeg-extension.md)).
- `T<a>(b)`, without a space between `>` and `(`, is a template call with
  the value argument `b`, not a template call followed by a group. A
  template cannot take value arguments yet, so such a call is the error
  `the template T takes no value arguments`; write `T<a> (b)` for the
  group. `ETemplate` has the value arguments as its last field
  ([ADR 0055](https://github.com/tett23/peg-hs/blob/main/docs/adr/0055-templates-and-parameterized-rules-in-stages.md)).

### Fixed

Since v0.1.0-rc1:

- A template call in a grammar without templates is the error
  `rule B is not a template`, not an internal error of the generator
  ([ADR 0052](https://github.com/tett23/peg-hs/blob/main/docs/adr/0052-template-calls-in-grammars-without-templates.md)).
- With `%syntax`, two rules with the same type name, such as `expr` and
  `Expr`, are an error; `syntaxTypeName` gives the name
  ([ADR 0053](https://github.com/tett23/peg-hs/blob/main/docs/adr/0053-type-names-of-rules-without-case.md)).
