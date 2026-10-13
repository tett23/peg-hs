# peg-hs

A PEG-to-Haskell parser generator with left recursion support.

[日本語版 README](README.ja.md)

- Accepts the full standard PEG syntax plus direct and indirect left recursion, based on bounded left recursion (Medeiros et al. 2014)
- Standalone code generator in the style of happy / alex: deterministically generates `.hs` from `.peg` (byte-identical output for identical input)
- Each rule carries a result type and semantic actions, so generated parsers return your AST directly
- Context-sensitive extensions (semantic predicates, parameterized rules, a read-only parse environment, and column references) for indentation-sensitive and forward-referencing syntax, designed so that packrat memoization and left recursion stay sound
- Type errors in semantic actions are reported at their line and column in the `.peg` file
- Optional lossless syntax trees in the style of rust-analyzer (`%syntax`), keeping every space and comment, for linters and formatters
- Error recovery with labelled failures (`e ^label` and `%recover`): a recovering parse always returns a lossless tree with error nodes, for language servers

**Status: pre-release (0.1).** The generator, the runtime and the conformance tests are implemented. Not yet published on Hackage.

- JSON ([JSONTestSuite](https://github.com/nst/JSONTestSuite)): all 95 must-accept and 188 must-reject cases pass
- CommonMark 0.31.2: all 652 spec examples pass
- Lua 5.5 (the official test suite of Lua 5.5.1): all 34 files are accepted, with the grammar of the manual written as indirect left recursion; precedence, associativity and rejections agree with the reference implementation on generated cases
- TOML 1.1.0 ([toml-test](https://github.com/toml-lang/toml-test) v2.2.0): all 214 valid documents match the expected JSON and all 467 invalid ones are rejected; every input gives a lossless tree when recovering

See [docs/specifications.md](docs/specifications.md) for the specification, [docs/syntax.md](docs/syntax.md) for the `.peg` notation with examples, and [docs/adr/](docs/adr/) for design decisions. These documents are currently written in Japanese.

## Usage

### Building the CLI

The command line tool `peg-hs` is built from the repository with the toolchain described in [Development](#development) (GHC 9.10.3 and cabal-install 3.16.1.0).

```sh
git clone https://github.com/tett23/peg-hs.git
cd peg-hs
cabal build exe:peg-hs
```

`cabal list-bin exe:peg-hs` prints the path of the built executable.
To install it into a directory on your `PATH`, for example `~/.local/bin`:

```sh
cabal install exe:peg-hs --installdir="$HOME/.local/bin" --install-method=copy --overwrite-policy=always
```

### Generating a parser

```sh
peg-hs gen Grammar.peg -o Grammar.hs
```

Without installing, run it through cabal instead:

```sh
cabal run peg-hs -- gen Grammar.peg -o Grammar.hs
```

The generated module depends only on the `peg-runtime` package and exports `parse :: Text -> Either ParseError a` for the start rule.

The generator warns about labels that may make the grammar reject valid input ([ADR 0028](docs/adr/0028-label-safety-check.md)). `--Werror` makes a warning fail the generation, and `%safe label` in the grammar silences the warning for a label checked by hand.

### Trying a grammar on an input

```sh
peg-hs parse Grammar.peg input.txt [--format ast|cst|all] [--entry RULE] [--ghc-arg ARG]...
```

`parse` shows the value of the start rule (the AST, by default) or the lossless syntax tree (the CST) of an input ([ADR 0036](docs/adr/0036-parse-command.md)).
It compiles the generated parser with the `ghc` on `PATH` (GHC 9.10) and caches the executable under `$XDG_CACHE_HOME/peg-hs/parse`, so only the first run with a grammar waits for GHC.
The AST needs a `Show` instance of the start rule's type.
When the grammar's Haskell code imports your modules, pass their directory with `--ghc-arg -isrc`, or run through `cabal exec -- peg-hs parse ...` to use the packages of a cabal project.

### Formatting grammars

```sh
peg-hs fmt [FILE...]
peg-hs fmt --check [FILE...]
```

`fmt` rewrites grammars in place in one fixed style, with no options ([ADR 0032](docs/adr/0032-grammar-formatter.md)).
Without files, it formats every `.peg` file under the current directory, skipping directories whose name starts with `.` and `dist-newstyle`.
`--check` writes nothing, lists the files that are not formatted, and fails if there are any.

### Linting grammars

```sh
peg-hs lint [FILE...]
```

`lint` warns about what is certainly a mistake in a grammar that passes the checks: alternatives that are never tried or never succeed, labels without effect inside lookaheads, and unused bindings ([ADR 0033](docs/adr/0033-grammar-linter.md)).
The rules are fixed and a warning cannot be silenced; each one goes away by changing the grammar, and any warning makes the command fail.
Without files, it lints the same files as `fmt`.

### Editors

`editors/` has the grammars for syntax highlighting ([ADR 0034](docs/adr/0034-syntax-highlighting.md)).
Haskell fragments (verbatim blocks, types, actions, predicates and arguments) are highlighted by the editor's Haskell grammar.

- **VS Code**: `editors/vscode` is an extension with the TextMate grammar (`editors/textmate/peg.tmLanguage.json`) that also starts the language server. Install its dependencies, link it into the extensions directory and restart VS Code. The setting `peg-hs.path` names the `peg-hs` executable:

  ```sh
  (cd editors/vscode && npm ci)
  ln -s "$PWD/editors/vscode" ~/.vscode/extensions/peg-hs
  ```

- **Neovim** (nvim-treesitter): register the tree-sitter grammar in `editors/tree-sitter-peg`, and copy its queries to `queries/peg/` in the runtime path:

  ```lua
  vim.filetype.add({ extension = { peg = 'peg' } })
  require('nvim-treesitter.parsers').get_parser_configs().peg = {
    install_info = { url = '/path/to/peg-hs/editors/tree-sitter-peg', files = { 'src/parser.c' } },
    filetype = 'peg',
  }
  ```

- **Helix**: add the language and the grammar to `languages.toml`, run `hx --grammar build`, and copy the queries to `runtime/queries/peg/`:

  ```toml
  [[language]]
  name = "peg"
  scope = "source.peg"
  file-types = ["peg"]
  comment-token = "#"

  [[grammar]]
  name = "peg"
  source = { path = "/path/to/peg-hs/editors/tree-sitter-peg" }
  ```

### Language server

`peg-hs lsp` is a language server on standard input and output ([ADR 0035](docs/adr/0035-language-server.md)).
It reports the errors and warnings of `gen` and `lint` as you type, formats with `fmt`, and provides semantic tokens, go to definition, references, hover and document symbols.
Besides the VS Code extension above, configure it in Neovim:

```lua
vim.lsp.config('peg_hs', { cmd = { 'peg-hs', 'lsp' }, filetypes = { 'peg' }, root_markers = { '.git' } })
vim.lsp.enable('peg_hs')
```

and in Helix's `languages.toml`:

```toml
[language-server.peg-hs]
command = "peg-hs"
args = ["lsp"]

[[language]]
name = "peg"
language-servers = ["peg-hs"]
```

## Development

See [CONTRIBUTING.md](CONTRIBUTING.md) for how changes are made: ADRs, tests first, commits and releases.

The toolchain is the one ghcup marks as recommended: GHC 9.10.3, cabal-install 3.16.1.0, and HLS 2.14.0.0.
`cabal.project` pins the compiler version.
If you use [mise](https://mise.jdx.dev/), the bundled `mise.toml` puts ghcup's binaries on the project's `PATH`.

```sh
ghcup install ghc 9.10.3
ghcup install cabal 3.16.1.0
```

After cloning, install [adr-guard](https://github.com/tett23/adr-guard) and enable the git hooks.
Committed ADRs and benchmark records (`docs/benchmarks/`) are immutable: adr-guard rejects changes to them in the pre-commit hook and in CI, except for the status line of an ADR and the links of its references to ADRs.
Each ADR has exactly one status line, a line starting with `ステータス:` ([ADR 0043](docs/adr/0043-adr-guard-v0.8.0.md)).

```sh
cargo install --git https://github.com/tett23/adr-guard --tag v0.8.1
git config core.hooksPath .githooks
```

Run all tests:

```sh
cabal test all
```

Generated modules are committed, and the tests check that they match the generator's current output.
After changing the generator or a grammar, regenerate them:

```sh
scripts/regen-fixtures.sh
```

The parser of the `.peg` notation is generated from the notation's own grammar, `packages/peg-grammar/grammar/Peg.peg` ([ADR 0027](docs/adr/0027-switch-to-self-hosted-parser.md)).
To add a construct to the notation and use it in `Peg.peg` itself, regenerate twice: first add the rules that accept the construct without using it, and regenerate; then use it in `Peg.peg`, and regenerate with the new generator.

Performance regressions are caught with local benchmarks.
For changes touching peg-runtime or peg-codegen, compare benchmark results before and after on the same machine ([ADR 0007](docs/adr/0007-performance-discipline.md)).

```sh
cabal bench peg-conformance
```

Before turning memoisation off for a rule with `%nomemo`, check where memo entries accumulate and compare peak memory in separate processes ([ADR 0017](docs/adr/0017-nomemo-implementation.md)):

```sh
cd conformance && $(cabal list-bin peg-conformance:bench:peg-bench) --memo-report
```

The CommonMark test takes options for inspecting results: `--show N` prints one example, `--report FILE` writes per-section results, and `--accept` records the current passing examples.

```sh
cd conformance && $(cabal list-bin peg-conformance:test:commonmark-conformance) --show 5
```

The editor grammars are tested with Node and the tree-sitter CLI. After changing the notation, update the grammars in `editors/`; the tests compare their ranges with those of the notation's own grammar, which `cabal test peg-grammar` writes to `editors/test/ranges.txt` with `--accept`:

```sh
cd editors && npm ci && npm test
```

The golden data of the Lua test is made with the reference implementation, Lua 5.5.1, which is needed only to regenerate it:

```sh
conformance/lua/golden/regen.sh
```

## License

[MIT](LICENSE)
