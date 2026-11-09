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

Since v0.1.0-rc2:

- `optExports` of `Options`: export only the entry points and the names of
  `%syntax` given, and leave out the declarations that only the other names
  use, so that the module still compiles without warnings. A name that the
  generator does not define is an error ([ADR 0061](https://github.com/tett23/peg-hs/blob/main/docs/adr/0061-select-generated-exports.md)).
- A module whose declarations `--export` leaves out turns off the warnings
  of unused imports and top-level bindings, which the code of the grammar
  used only by the left-out actions would get ([ADR 0062](https://github.com/tett23/peg-hs/blob/main/docs/adr/0062-warnings-of-pruned-generated-modules.md)).
- A rule without a type annotation is generated with type `()`. An action
  of such a rule that returns another type is a type error of GHC at the
  action ([ADR 0066](https://github.com/tett23/peg-hs/blob/main/docs/adr/0066-omit-unit-type-annotations.md)).
- An alternative of a rule of type `()` that omits its action because it
  has no value other than unit returns `()`
  ([ADR 0063](https://github.com/tett23/peg-hs/blob/main/docs/adr/0063-omit-unit-actions.md),
  [ADR 0064](https://github.com/tett23/peg-hs/blob/main/docs/adr/0064-unit-rules-always-return-unit.md)).
- In a grammar with `%syntax`, an alternative without an action of a rule
  without a type annotation returns `()` whatever its elements, such as a
  capture or a call of a rule with a type annotation. Its elements discard
  their values, and the bound ones stay bound for predicates and
  arguments. Grammars without `%syntax` are generated as before
  ([ADR 0068](https://github.com/tett23/peg-hs/blob/main/docs/adr/0068-untyped-rules-in-syntax-grammars.md)).

Since v0.1.0-rc3:

- The rules whose types are inferred return their values, and the rules
  whose types are generated return a constructor applied to the values
  of their elements. The generated types are declared and exported with
  their constructors (`Expr(..)`), with `deriving (Eq, Show)` or the
  classes of `%deriving`; with `optExports`, only the types that the
  types of the exported entry points refer to are exported
  ([ADR 0075](https://github.com/tett23/peg-hs/blob/main/docs/adr/0075-generated-types-for-rules-without-actions.md)).

Since v0.1.0-rc6:

- Libraries: `generateWithWarnings` takes the texts of the libraries
  that the grammar imports, and the `LINE` pragmas of the actions of a
  library name the library. `renderWarning` takes the imports of the
  grammar to name the file of a warning
  ([ADR 0092](https://github.com/tett23/peg-hs/blob/main/docs/adr/0092-import-rules-from-other-grammars.md)).
- `generateWithWarnings` and `Generation`, the steps of `peg-hs gen`
  without reading and writing files: parse, expand the templates, check,
  collect the warnings about labels and generate. `peg-hs gen` and
  peg-hooks both use them. `renderWarning` renders a warning as
  `file:line:column: warning: message`
  ([ADR 0085](https://github.com/tett23/peg-hs/blob/main/docs/adr/0085-generate-modules-in-the-build-with-setup-hooks.md)).
- A rule with `%expect` is generated with `PegRt.expecting` inside its
  memoising function, and a label with `%message` with
  `PegRt.labeledMessage` (`PegRt.labeledMessageS` with `%syntax`). The
  code of grammars without them does not change
  ([ADR 0089](https://github.com/tett23/peg-hs/blob/main/docs/adr/0089-rule-names-and-label-messages-in-errors.md)).

### Changed

Since v0.1.0-rc6:

- The memoising function of a rule and the labels of the children in the
  syntax tree are chosen by `ruleMemoisation` and `childLabel` of
  peg-grammar, which the interpreter of grammars uses too. The generated
  code does not change
  ([ADR 0090](https://github.com/tett23/peg-hs/blob/main/docs/adr/0090-grammar-interpreter-without-ghc.md)).

### Fixed

Since v0.1.0-rc1:

- With `%syntax`, a rule name that starts with a letter without upper
  case (kanji, kana, `_`) gets `Rule'` before its type name, so the module
  compiles ([ADR 0053](https://github.com/tett23/peg-hs/blob/main/docs/adr/0053-type-names-of-rules-without-case.md)).

Since v0.1.0-rc6:

- A label with a recovery rule where its value is not used discards the
  value of its expression as well as that of the recovery rule
  (`PegRt.voidS` or `PegRt.voidP`). The generated module did not compile
  when the expression had a value other than `()`: a reference to a rule
  with a value, or `?`, `*` and `+` with `%syntax`
  ([ADR 0094](https://github.com/tett23/peg-hs/blob/main/docs/adr/0094-fixes-of-recovered-labels-duplicate-alternatives-and-incremental-quotes.md)).

### Security

Since v0.1.0-rc5:

- `generate` returns the error `the file name contains a control
  character` at line 1, column 1 when `optSourceName` or `optOutputName`
  has a control character (U+0000 to U+001F, or U+007F), which could end
  the comment of the first line of the module. Other names generate the
  same bytes as before
  ([ADR 0080](https://github.com/tett23/peg-hs/blob/main/docs/adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).
