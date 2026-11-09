# Changelog of peg-cli

The format follows the release notes of peg-hs: each version lists what was
Added, Changed, Removed and Fixed, with the ADRs that decided it.

## 0.1.0.0

The first release. peg-cli provides the `peg-hs` executable, with
subcommands ([ADR 0037](https://github.com/tett23/peg-hs/blob/main/docs/adr/0037-cli-subcommands.md)).

### Added

- `peg-hs gen`: generate a Haskell module from a grammar
  ([ADR 0002](https://github.com/tett23/peg-hs/blob/main/docs/adr/0002-standalone-code-generator.md),
  [ADR 0014](https://github.com/tett23/peg-hs/blob/main/docs/adr/0014-generated-module-api.md)).
- `peg-hs fmt`: format grammars ([ADR 0032](https://github.com/tett23/peg-hs/blob/main/docs/adr/0032-grammar-formatter.md)).
- `peg-hs lint`: report what is likely a mistake in grammars
  ([ADR 0033](https://github.com/tett23/peg-hs/blob/main/docs/adr/0033-grammar-linter.md)).
- `peg-hs parse`: parse an input with a grammar and show the AST and the
  CST ([ADR 0036](https://github.com/tett23/peg-hs/blob/main/docs/adr/0036-parse-command.md)).
- `peg-hs lsp`: the language server
  ([ADR 0035](https://github.com/tett23/peg-hs/blob/main/docs/adr/0035-language-server.md)).
- `peg-hs help` and `peg-hs --version`.
- Examples in the help of every command, options as `--name=value`, and
  suggestions for misspelt commands
  ([ADR 0046](https://github.com/tett23/peg-hs/blob/main/docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)).
- Files are read and written as UTF-8 whatever the locale, and a file that
  cannot be read or written is reported in a line with hints;
  `fmt` and `lint` take directories
  ([ADR 0045](https://github.com/tett23/peg-hs/blob/main/docs/adr/0045-fixes-before-v0-1-0.md)).
- `peg-hs parse` takes GHC 9.10, 9.12 and 9.14, and shows text outside
  ASCII as itself ([ADR 0045](https://github.com/tett23/peg-hs/blob/main/docs/adr/0045-fixes-before-v0-1-0.md)).
- Builds with GHC 9.10, 9.12 and 9.14
  ([ADR 0045](https://github.com/tett23/peg-hs/blob/main/docs/adr/0045-fixes-before-v0-1-0.md)).

Since v0.1.0-rc1:

- `peg-hs label`: insert labels where the label check shows them to be
  safe, so that they do not change the language
  ([ADR 0054](https://github.com/tett23/peg-hs/blob/main/docs/adr/0054-automatic-label-insertion.md)).

Since v0.1.0-rc2:

- `peg-hs gen --export NAME`: export only the names given of those the
  generator defines, and generate only the declarations they need
  ([ADR 0061](https://github.com/tett23/peg-hs/blob/main/docs/adr/0061-select-generated-exports.md)).
- `peg-hs lint --verbose` also writes infos, with `info:` in place of
  `warning:`, for what can be simpler, such as a `{ () }` that can be
  omitted. Without `--verbose`, infos are not shown; they never make
  `lint` fail. `omittable-identity-action` notes an action that only
  returns a binding, as `e:Expr { e }`, and `omittable-unit-annotation` a
  type annotation `A :: ()`, which a rule without one has
  ([ADR 0066](https://github.com/tett23/peg-hs/blob/main/docs/adr/0066-omit-unit-type-annotations.md),
  [ADR 0065](https://github.com/tett23/peg-hs/blob/main/docs/adr/0065-omittable-identity-actions.md),
  [ADR 0063](https://github.com/tett23/peg-hs/blob/main/docs/adr/0063-omit-unit-actions.md),
  [ADR 0067](https://github.com/tett23/peg-hs/blob/main/docs/adr/0067-lint-info-with-verbose.md)).

Since v0.1.0-rc3:

- `peg-hs gen` infers or generates the types of the rules without type
  annotations and actions, and `peg-hs fmt` places `@Name` where an
  action goes
  ([ADR 0075](https://github.com/tett23/peg-hs/blob/main/docs/adr/0075-generated-types-for-rules-without-actions.md)).

Since v0.1.0-rc6:

- `peg-hs gen` takes `%expect` and `%message`, `peg-hs fmt` keeps the
  inside of their strings, and `peg-hs parse` shows the display names and
  the messages in its errors
  ([ADR 0089](https://github.com/tett23/peg-hs/blob/main/docs/adr/0089-rule-names-and-label-messages-in-errors.md)).
- `peg-hs parse --interpret` parses an input by interpreting the grammar,
  without `ghc` and without the cache, and shows the CST as
  `--format cst` does. `--format ast`, `--format all` and `--ghc-arg` are
  usage errors with it, and a grammar whose predicates it cannot evaluate
  is an error at each of them. It takes grammars with `%env` whose
  predicates do not read `_env`
  ([ADR 0090](https://github.com/tett23/peg-hs/blob/main/docs/adr/0090-grammar-interpreter-without-ghc.md)).
- `peg-hs test` parses the examples of a grammar, the inputs `X.in` in
  `NAME.cases/` beside `NAME.hpeg`, and compares the results with the
  expected syntax trees `X.cst` and errors `X.err`; an empty `X.err` only
  checks that the input is rejected, and `NAME.cases/RULE/` holds the
  examples of a rule of `%entry`. It fails with 1 when an example fails.
  `--accept` writes the results as the expectations. The examples are
  parsed by the interpreter, and a grammar that the interpreter cannot
  parse with is compiled as by `peg-hs parse`
  ([ADR 0091](https://github.com/tett23/peg-hs/blob/main/docs/adr/0091-grammar-test-command.md)).

### Changed

Since v0.1.0-rc1:

- Grammar files are `.hpeg`: `fmt` and `lint` look for `.hpeg` files, not
  `.peg` files, which other PEG tools use too. A file given by name is
  taken whatever its extension
  ([ADR 0050](https://github.com/tett23/peg-hs/blob/main/docs/adr/0050-hpeg-extension.md)).

Since v0.1.0-rc2:

- `peg-hs` runs with an allocation area of 64 MB (`-with-rtsopts=-A64m`).
  Parsing a grammar allocates about 40 MB, and with the default area most
  of the time of an edit in `peg-hs lsp` went to garbage collection
  ([ADR 0070](https://github.com/tett23/peg-hs/blob/main/docs/adr/0070-faster-checks-in-the-language-server.md)).

Since v0.1.0-rc6:

- `peg-hs gen` uses `generateWithWarnings` of peg-codegen, which peg-hooks
  uses too. What it writes and its exit status do not change
  ([ADR 0085](https://github.com/tett23/peg-hs/blob/main/docs/adr/0085-generate-modules-in-the-build-with-setup-hooks.md)).

### Security

Since v0.1.0-rc4:

- `fmt` and `lint` without files, or with a directory, no longer follow
  symbolic links to files or directories, so that they do not format files
  outside the directory searched, and end on cyclic links. A file given by
  name is still read and written through its link, and a directory given
  by name is searched even if it is a link
  ([ADR 0077](https://github.com/tett23/peg-hs/blob/main/docs/adr/0077-fixes-of-the-security-audit.md)).
- `peg-hs parse` makes its working directory by one `mkdir` with a random
  name and, on POSIX, the permission 0700; a name that is taken is never
  reused, and the directory is removed after a failure or an exception too.
  The executable depends on `unix` on POSIX
  ([ADR 0077](https://github.com/tett23/peg-hs/blob/main/docs/adr/0077-fixes-of-the-security-audit.md)).
