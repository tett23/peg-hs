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
  an error. A template may have value parameters, as
  `Indented<p>(n :: Int)`, called as `Indented<Item>(ind + 2)`
  ([ADR 0055](https://github.com/tett23/peg-hs/blob/main/docs/adr/0055-templates-and-parameterized-rules-in-stages.md)).
- `Peg.Grammar.LabelInsertion`: the positions where a label is shown to
  be safe, their names, the source with the labels inserted, and the
  recovery rules to propose for labels; `labelSafeAt` and `matchesEmpty`
  in `Peg.Grammar.Labels`
  ([ADR 0054](https://github.com/tett23/peg-hs/blob/main/docs/adr/0054-automatic-label-insertion.md)).

Since v0.1.0-rc2:

- In a rule of type `()`, an alternative with no value other than unit may
  omit its action, and its value is `()`, even when its only counted
  element is a repetition or an option of a unit rule
  ([ADR 0063](https://github.com/tett23/peg-hs/blob/main/docs/adr/0063-omit-unit-actions.md),
  [ADR 0064](https://github.com/tett23/peg-hs/blob/main/docs/adr/0064-unit-rules-always-return-unit.md)).
  `omitsUnitAction` in `Peg.Grammar.Check` tells such alternatives.
- The linter gives infos besides warnings (`LintLevel`, `lintLevel`):
  `omittable-unit-action` notes a `{ () }` that can be omitted, and
  `renderLintWarning` writes an info with `info:`
  ([ADR 0063](https://github.com/tett23/peg-hs/blob/main/docs/adr/0063-omit-unit-actions.md),
  [ADR 0067](https://github.com/tett23/peg-hs/blob/main/docs/adr/0067-lint-info-with-verbose.md)).
- The info `omittable-identity-action` of the linter notes an action that
  only returns a binding, as `e:Expr { e }`, where the alternative returns
  the same value without the binding and the action. It is not given in
  grammars with `%syntax`
  ([ADR 0065](https://github.com/tett23/peg-hs/blob/main/docs/adr/0065-omittable-identity-actions.md)).
- A rule without a type annotation has type `()`, which
  `rule A has no type annotation` used to reject. A rule with template
  parameters still needs one: `rule T has parameters, so it needs a type
  annotation`. `ruleAnnotation` of `Rule` is where the annotation starts,
  and `Nothing` for a rule without one. The info
  `omittable-unit-annotation` of the linter notes a type annotation `()`
  of a rule without parameters
  ([ADR 0066](https://github.com/tett23/peg-hs/blob/main/docs/adr/0066-omit-unit-type-annotations.md)).
- In a grammar with `%syntax`, an alternative without an action of a rule
  without a type annotation may have any number of elements with values;
  its value is `()`. `discardingRules` and `discardsValues` of
  `Peg.Grammar.Check` tell which rules and alternatives these are
  ([ADR 0068](https://github.com/tett23/peg-hs/blob/main/docs/adr/0068-untyped-rules-in-syntax-grammars.md)).
- The highlight kinds `HDirectiveRule`, `HDirectiveLabel` and
  `HModuleName` of `Peg.Grammar.Highlight` split the arguments of
  directives into the rule names, the labels and the module they name;
  the other arguments stay `HDirectiveArgument`
  ([ADR 0069](https://github.com/tett23/peg-hs/blob/main/docs/adr/0069-richer-highlighting-and-format-on-save.md)).
- `Peg.Grammar.Incremental` parses a grammar by its top-level fragments
  (`splitFragments`, `parseFragments`), reusing the fragments of the
  previous version; the results are those of `parseTops`, of the
  recovering parse and of `outline` of the whole text. `outlineFromTree`,
  `OutlinePart`, `outlinePart`, `shiftOutlinePart` and `joinOutline` of
  `Peg.Grammar.Outline` build an outline from parts
  ([ADR 0071](https://github.com/tett23/peg-hs/blob/main/docs/adr/0071-incremental-parsing-in-the-language-server.md)).

Since v0.1.0-rc3:

- In a grammar without `%syntax`, a rule without a type annotation and
  without actions has type `()` when no alternative has a value other
  than `()`, the type of its values when every alternative has one value
  of the same type, and otherwise a type generated for it, with a
  constructor for each alternative. `Peg.Grammar.Types` classifies the
  rules (`classify`, `Classification`, `RuleType`, `DataType`,
  `Constructor`) and writes their types; `analysisTypes` of `Analysis`
  has the classification
  ([ADR 0075](https://github.com/tett23/peg-hs/blob/main/docs/adr/0075-generated-types-for-rules-without-actions.md)).
- The constructor name `@Name` at the end of an alternative
  (`altConstructor` of `Alt`), and `%deriving`, the classes that the
  generated types derive (`grammarDeriving` of `Grammar`). The checks
  report a constructor name where no type is generated, a name that does
  not start with an upper case letter, a name used twice and a default
  name that is the name of another generated type
  ([ADR 0075](https://github.com/tett23/peg-hs/blob/main/docs/adr/0075-generated-types-for-rules-without-actions.md)).
- `Peg.Grammar.Constructors`: the edits that write out the default
  constructor names of a rule, and the highlight kinds `HConstructor`
  and `HClassName` of `Peg.Grammar.Highlight`
  ([ADR 0075](https://github.com/tett23/peg-hs/blob/main/docs/adr/0075-generated-types-for-rules-without-actions.md)).

Since v0.1.0-rc5:

- The checks report a reference to a binding of the rule that the code
  cannot see, at the name in the code: a predicate or an argument that
  refers to a binding on its right (`the predicate refers to y, which is
  bound to its right`), code that refers to a binding inside a group
  (`y is bound inside a group, which the code cannot see`), and code
  that refers to a binding of another alternative (`x is not bound in
  this alternative`). `codeVariables` of `Peg.Grammar` reads the
  variables of Haskell code lexically, with their locations
  ([ADR 0082](https://github.com/tett23/peg-hs/blob/main/docs/adr/0082-static-check-of-binding-references.md)).

Since v0.1.0-rc6:

- The directives `%expect Name "display name"` and `%message label
  "message"`, in `grammarExpects` and `grammarMessages` of `Grammar`, with
  their checks. `directiveComment` of `Peg.Grammar.Assemble` splits the
  line of a directive into its argument and its comment, and does not
  take a `#` inside the string of `%expect` and `%message` for a comment;
  the parser, the formatter and the highlighting use it. `stripLabels`
  removes `%message` and keeps `%expect`
  ([ADR 0089](https://github.com/tett23/peg-hs/blob/main/docs/adr/0089-rule-names-and-label-messages-in-errors.md)).
- `Peg.Grammar.Interpret`, an interpreter of grammars that needs no GHC:
  `interpreter` prepares a checked grammar, and `interpret`,
  `interpretRecover` and `interpretWith` parse an input with the
  functions of `Peg.Runtime.Internal` that generated code calls, so that
  the errors and the syntax trees are those of the generated parser of
  the grammar with `%syntax`. It evaluates predicates and arguments of
  the forms `True`, `False` and comparisons of integers, parameters and
  `_col`, and reports the others
  ([ADR 0090](https://github.com/tett23/peg-hs/blob/main/docs/adr/0090-grammar-interpreter-without-ghc.md)).
- `Memoisation`, `ruleMemoisation` and `childLabel` of `Peg.Grammar.Check`:
  how a rule is memoised and which elements label their children in the
  syntax tree, decisions that the generator and the interpreter share
  ([ADR 0090](https://github.com/tett23/peg-hs/blob/main/docs/adr/0090-grammar-interpreter-without-ghc.md)).

### Changed

Since v0.1.0-rc1:

- The notation is called the `.hpeg` notation, after the extension of its
  files ([ADR 0050](https://github.com/tett23/peg-hs/blob/main/docs/adr/0050-hpeg-extension.md)).
- `T<a>(b)`, without a space between `>` and `(`, is a template call with
  the value argument `b`, not a template call followed by a group; write
  `T<a> (b)` for the group. `ETemplate` has the value arguments as its
  last field
  ([ADR 0055](https://github.com/tett23/peg-hs/blob/main/docs/adr/0055-templates-and-parameterized-rules-in-stages.md)).

Since v0.1.0-rc3:

- An alternative without an action with two or more values, in a rule
  without a type annotation and without actions, is no longer an error:
  the rule gets a generated type. `unitRules` takes the grammar, and
  `hasValue` and `countedItems` are in `Peg.Grammar.Types`, still
  exported by `Peg.Grammar.Check`
  ([ADR 0075](https://github.com/tett23/peg-hs/blob/main/docs/adr/0075-generated-types-for-rules-without-actions.md)).
- A call of an undefined rule has no known value: next to `undefined rule
  X`, the checks no longer report the number of values of the
  alternatives that call it, nor errors of constructor names that depend
  on it. `classUnknown` of `Classification` has the rules whose types
  depend on undefined rules
  ([ADR 0075](https://github.com/tett23/peg-hs/blob/main/docs/adr/0075-generated-types-for-rules-without-actions.md)).

Since v0.1.0-rc5:

- The linter reads the code of actions, predicates and arguments with
  `codeVariables`: a binding whose name is only in a string, a character
  literal or a comment is `unused-binding`, which it was not before
  ([ADR 0082](https://github.com/tett23/peg-hs/blob/main/docs/adr/0082-static-check-of-binding-references.md)).

Since v0.1.0-rc6:

- The messages of the syntax errors of the notation are written with
  `%message` in `grammar/Peg.hpeg`. `labelMessage` of `Peg.Grammar.Parser`
  keeps the messages of `escape`, `action` and `argcode` only, which
  depend on the character at the error; the messages are unchanged
  ([ADR 0089](https://github.com/tett23/peg-hs/blob/main/docs/adr/0089-rule-names-and-label-messages-in-errors.md)).

### Fixed

Since v0.1.0-rc1:

- A template call in a grammar without templates is the error
  `rule B is not a template`, not an internal error of the generator
  ([ADR 0052](https://github.com/tett23/peg-hs/blob/main/docs/adr/0052-template-calls-in-grammars-without-templates.md)).
- With `%syntax`, two rules with the same type name, such as `expr` and
  `Expr`, are an error; `syntaxTypeName` gives the name
  ([ADR 0053](https://github.com/tett23/peg-hs/blob/main/docs/adr/0053-type-names-of-rules-without-case.md)).
- The label safety check compares alternatives with the other labels
  removed, so a label does not change the judgement of another; a template
  argument passed on to a template call is passed as it is, so a template
  that calls itself expands ([ADR 0056](https://github.com/tett23/peg-hs/blob/main/docs/adr/0056-label-insertion-and-template-deviations.md)).

Since v0.1.0-rc6:

- `insertLabels` checks the grammar with the labels inserted with
  `labelWarnings`, as `peg-hs gen` does, and leaves out the labels it
  warns about, until it warns about none of the labels inserted. The
  warnings of the labels already in the grammar stay. `peg-hs gen` warned
  about some labels that `peg-hs label` inserted in rules that call
  themselves: the check unfolds a later alternative to compare it with
  what has matched, and unfolding a label takes one of its levels, so the
  labels inserted made it give up sooner than on the grammar without them
  ([ADR 0086](https://github.com/tett23/peg-hs/blob/main/docs/adr/0086-inserted-labels-pass-the-label-check.md)).
- `labelWarnings` and `labelSafeAt` judge each label on the grammar with
  the other labels removed, as [ADR 0029](../../docs/adr/0029-label-safety-implementation-deviations.md) defines: the analysis is made from
  the grammar without labels, and the frames of a label lose the other
  labels. Other labels changed the verdict in two ways: unfolding a label
  took one of the levels of unfolding a later alternative, and a rule of
  literals with a label on a literal was not taken as literals. The
  verdicts on some labels change; a label may also be warned about now
  where other labels had made the check give up early
  ([ADR 0087](https://github.com/tett23/peg-hs/blob/main/docs/adr/0087-other-labels-do-not-change-the-label-check.md),
  [ADR 0088](https://github.com/tett23/peg-hs/blob/main/docs/adr/0088-correct-the-second-example-of-adr-0087.md)).

### Security

Since v0.1.0-rc5:

- The value of `%module` must be a module name, and the items of `%export`
  items of an export list; other values, which the generated module would
  have as written, are errors at the value: `%module expects a module
  name, but got X` and `%export expects export items, but got X`
  ([ADR 0080](https://github.com/tett23/peg-hs/blob/main/docs/adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).
- An expression nests at most 256 levels deep: each group, prefix and
  postfix operator, label and template call is a level. The parser of the
  notation stops before a level over the limit with the error `the
  expression nests deeper than 256`, so a deeper grammar is rejected in
  time linear in its length, by every path through `parseTops`
  ([ADR 0080](https://github.com/tett23/peg-hs/blob/main/docs/adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).
