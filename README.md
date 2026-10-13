# peg-hs

peg-hs is a toolchain that generates Haskell parsers from grammars written as PEGs (Parsing Expression Grammars).

[日本語の README](README.ja.md)

## Overview

A grammar is written in a `.hpeg` file.
Each rule has a result type and semantic actions: Haskell expressions that make the value of the rule when it succeeds.
`peg-hs gen` generates a Haskell module from the grammar, and a program calls the `parse` of that module to get its own AST directly.

Compared with other parser generators, peg-hs has these features:

- **Left recursion as written**: direct and indirect left recursion, such as `Expr <- Expr '+' Term / Term`, is accepted. The semantics is bounded left recursion (Medeiros et al. 2014) ([ADR 0001](docs/adr/0001-bounded-left-recursion.md)).
- **Small dependencies of generated modules**: a generated module depends only on the runtime library peg-runtime. The same grammar generates the same module byte for byte, so generated modules can be committed ([ADR 0002](docs/adr/0002-standalone-code-generator.md)).
- **Type errors at the lines of the grammar**: GHC reports type errors in actions at the line and column of the `.hpeg` file ([ADR 0014](docs/adr/0014-generated-module-api.md)).
- **Context-sensitive syntax**: semantic predicates, parameterized rules, a read-only parse environment and column references express indentation-sensitive syntax and forward references, while keeping packrat memoization and left recursion correct ([ADR 0012](docs/adr/0012-context-sensitive-extensions.md)).
- **Syntax trees that keep whitespace and comments**: with `%syntax`, a lossless syntax tree in the style of rust-analyzer is built too, for tools such as formatters and linters ([ADR 0019](docs/adr/0019-lossless-syntax-tree.md)).
- **Recovery from syntax errors**: labelled failures (`e ^label` and `%recover`) report several errors in one parse. The recovering mode always returns a lossless syntax tree with error nodes, for language servers ([ADR 0021](docs/adr/0021-error-recovery.md)).

Grammars of real languages check the conformance:

- **JSON** ([JSONTestSuite](https://github.com/nst/JSONTestSuite)): all 95 must-accept and all 188 must-reject cases pass.
- **CommonMark 0.31.2**: all 652 examples of the specification conform.
- **Lua 5.5** (the official test suite of Lua 5.5.1): a grammar that keeps the manual's syntax with its indirect left recursion accepts all 34 files. Precedence, associativity and rejection agree with expectations made from the reference implementation.
- **TOML 1.1.0** ([toml-test](https://github.com/toml-lang/toml-test) v2.2.0): all 214 valid cases match the expected JSON, and all 467 invalid cases are rejected. The recovering mode returns a lossless syntax tree for every case.

**Status**: the first release candidate, v0.1.0-rc1, is distributed on GitHub [Releases](https://github.com/tett23/peg-hs/releases).
It is not on Hackage yet ([ADR 0044](docs/adr/0044-release-v0-1-0.md)).

## Installation

### Executables

GitHub [Releases](https://github.com/tett23/peg-hs/releases) has `peg-hs` for Linux (x86-64) and macOS (arm64).
Extract the archive and put `peg-hs` in a directory on `PATH`.
`SHA256SUMS` of the same release checks that the archive is intact.

```sh
tar xzf peg-hs-0.1.0-rc1-x86_64-linux.tar.gz
install peg-hs-0.1.0-rc1-x86_64-linux/peg-hs ~/.local/bin/
peg-hs --version
```

### From source

On other platforms, build from source.
It needs GHC 9.10, 9.12 or 9.14, and cabal-install ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).

```sh
git clone https://github.com/tett23/peg-hs.git
cd peg-hs
cabal install exe:peg-hs --installdir="$HOME/.local/bin" --install-method=copy --overwrite-policy=always
```

## A first grammar

This section generates and uses a grammar of expressions with addition, multiplication and parentheses.
Put the following grammar in `grammar/Calc.hpeg`.

<!-- readme-example: grammar/Calc.hpeg -->
```hpeg
%module Calc.Parser
%{
import qualified Data.Text as T

data Expr = Num Int | Add Expr Expr | Mul Expr Expr
  deriving (Show)
}%

# Addition binds looser than multiplication, and both associate to the left,
# as written with left recursion.
Expr :: Expr
Expr <- l:Expr '+' Sp r:Term { Add l r }
     / Term

Term :: Expr
Term <- l:Term '*' Sp r:Atom { Mul l r }
     / Atom

Atom :: Expr
Atom <- d:$[0-9]+ Sp { Num (read (T.unpack d)) }
     / '(' Sp e:Expr ')' Sp { e }

Sp :: ()
Sp <- ' '* { () }
```

`%module` is the name of the generated module.
Between `%{` and `}%` (a verbatim block) is Haskell that goes into the generated module as it is.
`Expr :: Expr` is the result type of the rule `Expr`, and `Expr <- ...` defines the rule.
`l:Expr` names a result (a binding), and `{ Add l r }` is an action.
`$[0-9]+` takes the text it read (a `Text`) as its value.
[docs/syntax.md](docs/syntax.md) explains the notation in detail (in Japanese).

Generate the module with `peg-hs gen`.

```sh
peg-hs gen grammar/Calc.hpeg -o src/Calc/Parser.hs
```

A generated module records the paths given to `gen`: in the comment at its top, and in `LINE` pragmas that point the errors of GHC at the lines of the grammar.
Give paths relative to the directory of the package that compiles the module.
cabal runs GHC in that directory, so editors can open the grammar from the location of an error, and the module is the same on every machine ([ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)).

To try the grammar before putting the module in a project, `peg-hs parse` parses an input with it.

```sh
echo -n '1 + 2 * (3 + 4)' > input.txt
peg-hs parse grammar/Calc.hpeg input.txt
```

```text
Add (Num 1) (Mul (Num 2) (Add (Num 3) (Num 4)))
```

## Using a generated module

A generated module exports the entry point of the start rule, `parse :: Text -> Either ParseError a`.
`a` is the type of the start rule: the first rule, or the one that `%start` names.
When parsing fails, `ParseError` has the farthest position that was read and the set of tokens expected there.
`renderParseError` of `Peg.Runtime` turns it into a line such as `1:4: expected ' ', '(' or [0-9]`.

This program parses a line of standard input and shows the AST or the error.

<!-- readme-example: src/Main.hs -->
```haskell
module Main (main) where

import Calc.Parser (parse)
import qualified Data.Text.IO as TIO
import Peg.Runtime (renderParseError)

main :: IO ()
main = do
  input <- TIO.getLine
  case parse input of
    Right expr -> print expr
    Left err -> TIO.putStrLn (renderParseError err)
```

The `.cabal` file of the package adds peg-runtime and text to `build-depends`.
The comment at the top of a generated module names the versions of peg-runtime it needs (`-- It needs peg-runtime >=0.1 && <0.2.`).

```cabal
executable calc
  main-is:          Main.hs
  hs-source-dirs:   src
  other-modules:    Calc.Parser
  build-depends:
    , base
    , peg-runtime  >=0.1 && <0.2
    , text
  default-language: GHC2021
```

peg-runtime is not on Hackage yet.
Until it is, point `cabal.project` at the GitHub repository, with the tag of the release of peg-hs to use.

```cabal
packages: .

source-repository-package
  type:     git
  location: https://github.com/tett23/peg-hs
  tag:      v0.1.0-rc1
  subdir:   packages/peg-runtime
```

After changing the grammar, generate the module again with `peg-hs gen` and commit it too.
Since the module follows from the grammar, generating it again in CI and checking that nothing changed catches a forgotten generation.

A generated module also exports:

- the entry points of the rules that `%entry` names (such as `parseExpr`);
- with `%syntax`, `parseSyntax`, which returns the lossless syntax tree ([ADR 0019](docs/adr/0019-lossless-syntax-tree.md));
- with `%recover`, `parseRecover`, which recovers from errors and returns all of them, and, with `%syntax` too, `parseSyntaxRecover`, which returns the syntax tree with error nodes ([ADR 0021](docs/adr/0021-error-recovery.md));
- with `%env`, every entry point takes the value of the parse environment as its first argument ([ADR 0012](docs/adr/0012-context-sensitive-extensions.md)).

The Haddock of `Peg.Codegen` (peg-codegen) and `Peg.Runtime` (peg-runtime) has the full list.

## Commands

`peg-hs` has a subcommand for each purpose ([ADR 0037](docs/adr/0037-cli-subcommands.md)).
`peg-hs help COMMAND` shows the options and examples of a command.
An option that takes a value takes it as `--output FILE` or as `--output=FILE`.
Files are read and written as UTF-8, whatever the locale ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).

| Command | Purpose |
|---|---|
| `peg-hs gen GRAMMAR.hpeg [-o FILE]` | generate a Haskell module from a grammar |
| `peg-hs fmt [FILE\|DIR...]` | format grammars in one style |
| `peg-hs lint [FILE\|DIR...]` | warn of what is a mistake in grammars |
| `peg-hs parse GRAMMAR.hpeg INPUT` | parse an input and show its AST or syntax tree |
| `peg-hs lsp` | run the language server on standard input and output |

The exit status is 0 on success and 2 for a mistake in the use of a command.
It is 1 for an error in a grammar, a file that cannot be read or written, a warning of `lint`, an unformatted file found by `fmt --check`, and a warning with `gen --Werror`.

### gen

`gen` checks the grammar and writes the module.
Without an output path, it is the grammar's path with the extension `.hs`.

The generator warns of labels that may reject valid input ([ADR 0028](docs/adr/0028-label-safety-check.md)).
With `--Werror`, a warning makes it fail without writing the module.
`%safe label` in the grammar silences the warning of a label that the author checked.

### fmt

`fmt` formats grammars in place, in one fixed style ([ADR 0032](docs/adr/0032-grammar-formatter.md)).
No option chooses the style. Comments are kept.
`--check` writes nothing; it lists the files that are not formatted, and fails if there are any. It is for checks in CI.

A directory among the arguments stands for the `.hpeg` files under it.
Files with the old extension `.peg` are not looked for, since other PEG tools use it too; a file given by name is taken whatever its extension ([ADR 0050](docs/adr/0050-hpeg-extension.md)).
Without arguments, `fmt` takes every `.hpeg` file under the current directory.
Either way, directories whose name starts with `.` and `dist-newstyle` are skipped.

### lint

`lint` warns of what is a mistake in grammars that pass the static checks ([ADR 0033](docs/adr/0033-grammar-linter.md)):
alternatives that are never tried or never succeed, alternatives that are the same as an earlier one, labels without effect inside a lookahead, and bindings that are not used.
The rules are fixed, and no warning can be silenced: every warning goes away by fixing the grammar, and any warning makes `lint` fail.
It chooses files as `fmt` does.

### parse

`parse` parses an input and shows the value of the start rule (the AST, by default) or the lossless syntax tree (the CST, with `--format cst`) ([ADR 0036](docs/adr/0036-parse-command.md)).
It compiles the generated parser with the `ghc` on `PATH` and caches the executable under `$XDG_CACHE_HOME/peg-hs/parse`, so GHC runs only the first time for each grammar.

- The AST needs a `Show` instance of the type of the start rule. Without one, use `--format cst`.
- `--entry RULE` parses with a rule of `%entry`.
- When the Haskell of the grammar imports modules of the project, pass the search path, as in `--ghc-arg -isrc`. To use the packages of a cabal project, run `cabal exec -- peg-hs parse ...`.
- Characters outside ASCII in strings are shown as themselves, not as escapes.

### lsp

`lsp` is a language server that speaks the Language Server Protocol on standard input and output ([ADR 0035](docs/adr/0035-language-server.md)).
Editors run it; the next section has their settings.

## Editors

`editors/` has grammars for syntax highlighting and a VS Code extension ([ADR 0034](docs/adr/0034-syntax-highlighting.md)).
The Haskell of a grammar (verbatim blocks, types, actions, semantic predicates, arguments) is highlighted by the editor's Haskell grammar.

The language server `peg-hs lsp` reports the errors and warnings of `gen` and `lint` as a grammar is edited, and formats it with `fmt`.
It also provides semantic tokens, go to definition, find references, hover and document symbols.

None of the settings below has been checked by hand in the editor yet (**unchecked**).
The results of checks go to `docs/editors/`, and an editor loses this mark when its check is recorded ([ADR 0044](docs/adr/0044-release-v0-1-0.md)).

### VS Code (unchecked)

`editors/vscode` is an extension with the TextMate grammar (`editors/textmate/hpeg.tmLanguage.json`) that starts the language server.
It is not on the Marketplace yet, so install it from the repository: install its dependencies, link it into the directory of extensions, and restart VS Code.
If `peg-hs` is not on `PATH`, the setting `peg-hs.path` points at the executable.

```sh
(cd editors/vscode && npm ci)
ln -s "$PWD/editors/vscode" ~/.vscode/extensions/peg-hs
```

### Neovim (unchecked)

For highlighting, register the tree-sitter grammar `editors/tree-sitter-hpeg` with nvim-treesitter (the main branch).
A `User TSUpdate` autocommand gives the path of the grammar and its directory of queries; then run `:TSInstall hpeg` in Neovim.
Building the grammar needs the tree-sitter CLI.
nvim-treesitter does not turn highlighting on by itself, so a `FileType` autocommand calls `vim.treesitter.start()`.

```lua
vim.filetype.add({ extension = { hpeg = 'hpeg' } })
vim.api.nvim_create_autocmd('User', { pattern = 'TSUpdate', callback = function()
  require('nvim-treesitter.parsers').hpeg = {
    install_info = { path = '/path/to/peg-hs/editors/tree-sitter-hpeg', queries = 'queries' },
  }
end })
vim.api.nvim_create_autocmd('FileType', { pattern = 'hpeg', callback = function() vim.treesitter.start() end })
```

With the old version of nvim-treesitter (the master branch), register it with `get_parser_configs()`.
The grammar has an external scanner (`src/scanner.c`), so `files` lists two files; copy the queries to `queries/hpeg/` on the runtime path.

```lua
require('nvim-treesitter.parsers').get_parser_configs().hpeg = {
  install_info = { url = '/path/to/peg-hs/editors/tree-sitter-hpeg', files = { 'src/parser.c', 'src/scanner.c' } },
  filetype = 'hpeg',
}
```

The language server is set up with `vim.lsp.config` of Neovim 0.11 or later.

```lua
vim.lsp.config('peg_hs', { cmd = { 'peg-hs', 'lsp' }, filetypes = { 'hpeg' }, root_markers = { '.git' } })
vim.lsp.enable('peg_hs')
```

### Helix (unchecked)

Add the language, the grammar and the language server to `languages.toml`, and run `hx --grammar build`.
Copy the queries to `runtime/queries/hpeg/`.

```toml
[[language]]
name = "hpeg"
scope = "source.hpeg"
file-types = ["hpeg"]
comment-token = "#"
language-servers = ["peg-hs"]

[[grammar]]
name = "hpeg"
source = { path = "/path/to/peg-hs/editors/tree-sitter-hpeg" }

[language-server.hpeg-hs]
command = "peg-hs"
args = ["lsp"]
```

## Migrating from the extension .peg

Grammar files were `.peg` until v0.1.0-rc1; they are `.hpeg` now, and the language of the editors is `hpeg` ([ADR 0050](docs/adr/0050-hpeg-extension.md)).

1. Rename the grammars: `git mv Grammar.peg Grammar.hpeg`.
2. Generate the modules again with the new paths, since a generated module records the path of its grammar.
3. Change the editor settings: the language and file type `peg` becomes `hpeg`, the tree-sitter grammar is `editors/tree-sitter-hpeg`, and the queries go to `queries/hpeg/`.

## Known limitations

- **Distribution**: executables are for Linux (x86-64) and macOS (arm64) only. On Windows, build from source. The packages are not on Hackage yet ([ADR 0044](docs/adr/0044-release-v0-1-0.md)).
- **Versions of GHC**: the packages and generated modules are checked with GHC 9.10, 9.12 and 9.14. GHC 9.8 and earlier are not supported ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).
- **Encoding**: grammars and inputs must be UTF-8. Convert files in other encodings first ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).
- **`peg-hs parse` and `%env`**: `parse` cannot handle grammars with `%env` (the read-only parse environment), since it has no way to give the value of the environment. Check such grammars by calling the generated module from a program ([ADR 0036](docs/adr/0036-parse-command.md)).
- **GHC for `peg-hs parse`**: `parse` compiles the parser with the `ghc` on `PATH`, which must be GHC 9.10, 9.12 or 9.14 ([ADR 0036](docs/adr/0036-parse-command.md), [ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).
- **Rules whose type names collide**: with `%syntax`, each rule has a type named after it, so two rules such as `expr` and `Expr` are an error. `peg-hs parse` always generates the syntax tree too, so it rejects such grammars even without `%syntax` ([ADR 0053](docs/adr/0053-type-names-of-rules-without-case.md)).
- **The check of labels is conservative**: it does not miss labels that may reject valid input, and in exchange it may warn of labels that are in fact safe. `%safe` silences the warning of a label that the author checked. The grammar of the notation itself has 21 `%safe` ([ADR 0028](docs/adr/0028-label-safety-check.md), [ADR 0038](docs/adr/0038-label-check-precision-and-strip-labels-entries.md)).
- **Rule templates**: a template cannot take the arguments of parameterized rules, and cannot be a rule of `%entry`, `%start` or `%recover` ([ADR 0031](docs/adr/0031-rule-templates.md); combining them was rejected in [ADR 0040](docs/adr/0040-templates-with-parameterized-rules.md)).
- **The tree-sitter grammar**: an alternative with neither elements nor an action (`S <- 'a' /`) is an error. Such an alternative has no value, so `peg-hs gen` always rejects it too, and no valid grammar is shown as an error ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).
- **The TextMate grammar**: its rules are regular expressions, so distinctions that depend on the context (the call `A(x)` and the sequence `A (x)`) are approximate. The semantic tokens of the language server distinguish them exactly ([ADR 0034](docs/adr/0034-syntax-highlighting.md)).
- **Editor settings**: the settings of the three editors above are not checked by hand yet ([ADR 0044](docs/adr/0044-release-v0-1-0.md)). The VS Code extension is not on the Marketplace.

## Documents

- [docs/syntax.md](docs/syntax.md): the `.hpeg` notation, with examples (in Japanese)
- [docs/specifications.md](docs/specifications.md): the specification of the product (in Japanese)
- [docs/adr/](docs/adr/): the records of design decisions (ADRs), in Japanese. Each item of the specification can be traced to its decision.
- [CONTRIBUTING.md](CONTRIBUTING.md): the development environment, tests, regenerating generated files, ADRs, commits and the release procedure
- `CHANGELOG.md` of each package: the changes of each version

## License

[MIT](LICENSE).
The test data under `conformance/data/` follows the LICENSE in each of its directories.
