# Editor grammars of peg-hs

Syntax highlighting for `.hpeg` grammars, in two forms
([ADR 0034](https://github.com/tett23/peg-hs/blob/main/docs/adr/0034-syntax-highlighting.md),
[ADR 0069](https://github.com/tett23/peg-hs/blob/main/docs/adr/0069-richer-highlighting-and-format-on-save.md)).
Releases carry them in `peg-hs-editors-<version>.tar.gz`, and under `editors/` in the archives of the executable
([ADR 0073](https://github.com/tett23/peg-hs/blob/main/docs/adr/0073-editor-grammars-in-releases.md)).

- `textmate/hpeg.tmLanguage.json`: the TextMate grammar, scope `source.hpeg`, for editors that read TextMate grammars.
- `tree-sitter-hpeg/`: the tree-sitter grammar, with the generated parser in `src/` and the queries in `queries/`.
  Neovim and Helix build the parser from `src/parser.c` and `src/scanner.c`; the tree-sitter CLI and Node.js are not needed.

The Haskell of a grammar (verbatim blocks, types, actions, semantic predicates, arguments) is highlighted by the editor's Haskell grammar.

## Setting up an editor

The section Editors of the README of peg-hs has the settings for VS Code, Neovim and Helix, with the language server `peg-hs lsp`:
https://github.com/tett23/peg-hs#editors

Where those settings name `/path/to/peg-hs/editors/tree-sitter-hpeg`, use the `tree-sitter-hpeg/` of this directory.
For Helix, copy `highlights.scm`, `injections.scm` and `locals.scm` of `tree-sitter-hpeg/queries/` to `runtime/queries/hpeg/`.
