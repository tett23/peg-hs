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

### Changed

Since v0.1.0-rc1:

- Grammar files are `.hpeg`: `fmt` and `lint` look for `.hpeg` files, not
  `.peg` files, which other PEG tools use too. A file given by name is
  taken whatever its extension
  ([ADR 0050](https://github.com/tett23/peg-hs/blob/main/docs/adr/0050-hpeg-extension.md)).
