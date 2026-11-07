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

Since v0.1.0-rc2:

- The severity `Hint` of a diagnostic, for the infos of the linter
  ([ADR 0063](https://github.com/tett23/peg-hs/blob/main/docs/adr/0063-omit-unit-actions.md),
  [ADR 0067](https://github.com/tett23/peg-hs/blob/main/docs/adr/0067-lint-info-with-verbose.md)).
- The hover of a rule without a type annotation shows its type `()`
  ([ADR 0066](https://github.com/tett23/peg-hs/blob/main/docs/adr/0066-omit-unit-type-annotations.md)).
- Changes that arrive faster than the server checks them are coalesced:
  the server sends the diagnostics of a changed document when no more
  input is waiting, for its latest version only. Requests are still
  answered in order, for the latest version. `receiveFrame`,
  `receiveMessage` and `publishPending` expose this; `handleFrame` and
  `handleMessage` still send the diagnostics with each change
  ([ADR 0070](https://github.com/tett23/peg-hs/blob/main/docs/adr/0070-faster-checks-in-the-language-server.md)).
- An edit is checked faster: the grammar is parsed once per version, the
  outline and the diagnostics of a version are computed once and shared,
  lines are looked up in logarithmic time, JSON strings are written by
  runs, and the lexical rules of the JSON parser are not memoised. The
  diagnostics are unchanged
  ([ADR 0070](https://github.com/tett23/peg-hs/blob/main/docs/adr/0070-faster-checks-in-the-language-server.md)).
- Semantic tokens for the arguments of directives: the rule names of
  `%start`, `%entry`, `%nomemo`, `%token`, `%trivia`, `%inline` and
  `%recover` are `function`, the labels of `%recover` and `%safe` are
  `decorator`, and the argument of `%module` is `namespace`, a new token
  type of the legend
  ([ADR 0069](https://github.com/tett23/peg-hs/blob/main/docs/adr/0069-richer-highlighting-and-format-on-save.md)).
- Text synchronisation is incremental (`TextDocumentSyncKind.Incremental`):
  a change carries a range in the position encoding of the server, UTF-16
  or UTF-8, and its text; several changes of one notification apply in
  order, and a position past the end of a line or of the document is its
  end. Each version is parsed by its top-level items, reusing the results
  of the items that did not change; the diagnostics and the outline are
  those of parsing the whole document. `documentText` and
  `reparsedFragments` expose the text and the number of parsed fragments
  of a document for tests
  ([ADR 0071](https://github.com/tett23/peg-hs/blob/main/docs/adr/0071-incremental-parsing-in-the-language-server.md)).

Since v0.1.0-rc3:

- The semantic tokens `enumMember` for constructor names and `type` for
  the classes of `%deriving`; the hover of a rule shows the type inferred
  or the declaration of the type generated for it, and the hover of a
  constructor name its type; a code action writes out the default
  constructor names of a rule
  ([ADR 0075](https://github.com/tett23/peg-hs/blob/main/docs/adr/0075-generated-types-for-rules-without-actions.md)).

### Changed

Since v0.1.0-rc4:

- `decodeFrames` returns the bytes left over, or a `FrameError` when a
  message is over the limits `maxHeaderLength` (64 KiB) or
  `maxContentLength` (64 MiB); `renderFrameError` gives its reason
  ([ADR 0077](https://github.com/tett23/peg-hs/blob/main/docs/adr/0077-fixes-of-the-security-audit.md)).

### Security

Since v0.1.0-rc4:

- The language server keeps at most the limits of a message for a message
  that has not arrived in full: a header without its end over 64 KiB, or a
  `Content-Length` over 64 MiB, ends the server with the status 1 and the
  reason on the standard error
  ([ADR 0077](https://github.com/tett23/peg-hs/blob/main/docs/adr/0077-fixes-of-the-security-audit.md)).
