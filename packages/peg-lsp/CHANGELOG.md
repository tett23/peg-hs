# Changelog of peg-lsp

The format follows the release notes of peg-hs: each version lists what was
Added, Changed, Removed and Fixed, with the ADRs that decided it.

## 0.1.0.0

The first release. peg-lsp is the language server of `.hpeg` grammars, run
by `peg-hs lsp` ([ADR 0035](https://github.com/tett23/peg-hs/blob/main/docs/adr/0035-language-server.md)).

### Added

- Diagnostics of syntax errors, static checks and the linter, while the
  grammar is being edited.
- Formatting ([ADR 0032](https://github.com/tett23/peg-hs/blob/main/docs/adr/0032-grammar-formatter.md)), go to
  definition, hover, document symbols and semantic tokens.
- The JSON and JSON-RPC that the server needs, without dependencies on
  other LSP libraries.
- Builds with GHC 9.10, 9.12 and 9.14
  ([ADR 0045](https://github.com/tett23/peg-hs/blob/main/docs/adr/0045-fixes-before-v0-1-0.md)).

Since v0.1.0-rc1:

- Code actions that insert the labels of `peg-hs label`, and that add
  `%recover` with a skeleton of a recovery rule to a label without one
  ([ADR 0054](https://github.com/tett23/peg-hs/blob/main/docs/adr/0054-automatic-label-insertion.md)).
