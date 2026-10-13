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
