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

**Status**: release candidates (the latest is v0.1.0-rc4) are distributed on GitHub [Releases](https://github.com/tett23/peg-hs/releases).
It is not on Hackage yet ([ADR 0044](docs/adr/0044-release-v0-1-0.md)).

## Installation

### Executables

GitHub [Releases](https://github.com/tett23/peg-hs/releases) has `peg-hs` for Linux (x86-64) and macOS (arm64).
Extract the archive and put `peg-hs` in a directory on `PATH`.
`SHA256SUMS` of the same release checks that the archive is intact.
The archive also has the editor grammars in `editors/` ([Editors](#editors)).

```sh
tar xzf peg-hs-0.1.0-rc4-x86_64-linux.tar.gz
install peg-hs-0.1.0-rc4-x86_64-linux/peg-hs ~/.local/bin/
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
     / '(' Sp Expr ')' Sp

Sp <- ' '*
```

`%module` is the name of the generated module.
Between `%{` and `}%` (a verbatim block) is Haskell that goes into the generated module as it is.
`Expr :: Expr` is the result type of the rule `Expr`, and `Expr <- ...` defines the rule.
A rule without a type annotation and without values, such as `Sp`, has type `()`; rules with parameters and templates need one ([ADR 0066](docs/adr/0066-omit-unit-type-annotations.md)).
`l:Expr` names a result (a binding), and `{ Add l r }` is an action.
`$[0-9]+` takes the text it read (a `Text`) as its value.
[docs/syntax.en.md](docs/syntax.en.md) explains the notation in detail.

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

### Three styles: generated types, a syntax tree, or typed values

A grammar is written in one of three styles, and a grammar without `%syntax` can mix the first and the third rule by rule.
The grammar above returns typed values: its rules have type annotations and actions.

Without type annotations and actions, peg-hs decides the types of the values from the grammar ([ADR 0075](docs/adr/0075-generated-types-for-rules-without-actions.md)).

```hpeg
%module Calc.Generated

Expr <- Expr '+' Sp Term @Add
     / Term

Term <- Term '*' Sp Atom @Mul
     / Atom

Atom <- Num
     / '(' Sp Expr ')' Sp

Num <- $[0-9]+ Sp

Sp <- ' '*
```

A rule whose alternatives have no value but `()`, such as `Sp`, has type `()`.
A rule whose alternatives have one value each, all of one type, has that type: `Num` returns the `Text` of `$[0-9]+`.
Any other rule gets a type generated for it, with a constructor for each alternative and `deriving (Eq, Show)`, which `%deriving` changes: `Expr` and `Term` have alternatives with two values and one, and the values of `Atom` are a `Text` and an `Expr`.
`@Add` names the constructor of an alternative; without it, the names are the type name and the number of the alternative (`Expr2`).
The module declares and exports these types:

```haskell
data Expr = Add Expr Term | Expr2 Term
  deriving (Eq, Show)

data Term = Mul Term Atom | Term2 Atom
  deriving (Eq, Show)

data Atom = Atom1 Text | Atom2 Expr
  deriving (Eq, Show)
```

The second style writes `%syntax` and neither type annotations nor actions, and reads the results from the lossless syntax tree that `parseSyntax` returns ([ADR 0068](docs/adr/0068-untyped-rules-in-syntax-grammars.md)).

```hpeg
%module Calc.Syntax
%syntax
%token Num

Expr <- Expr '+' Sp Term
     / Term

Term <- Term '*' Sp Atom
     / Atom

Atom <- Num Sp
     / '(' Sp Expr ')' Sp

Num <- $[0-9]+

Sp <- ' '*
```

In a grammar with `%syntax`, an alternative without an action of a rule without a type annotation has the value `()`, whatever the values of its elements, such as the capture `$[0-9]+`.
Write type annotations and actions only where typed values are needed.

The styles differ in cost.
On a JSON document of 800,000 characters, compared with the typed grammar without `%syntax`, the style with generated types took about 0.97 times the time and 1.18 times the peak live memory, without converting the generated values to other types ([docs/benchmarks/2026-11-06-json-generated-types.md](docs/benchmarks/2026-11-06-json-generated-types.md)); the style with the syntax tree took about 1.2 times the time and 1.2 times the memory in the same measurement ([docs/benchmarks/2026-11-06-json-generated-types.md](docs/benchmarks/2026-11-06-json-generated-types.md); an earlier measurement gave 1.6 and 1.1 times, [docs/benchmarks/2026-11-06-json-untyped-syntax.md](docs/benchmarks/2026-11-06-json-untyped-syntax.md)).
When speed matters, write type annotations and actions, and leave out `%syntax`; in a grammar without `%syntax`, this can be done for the rules that take the time only.

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
  tag:      v0.1.0-rc4
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
`gen --export` narrows the entry points and the names of `%syntax` to those a program uses ([ADR 0061](docs/adr/0061-select-generated-exports.md)).

## Generating the module in the build

Instead of generating the module with `peg-hs gen` and committing it, a cabal package can generate it in its own build, with the package peg-hooks ([ADR 0085](docs/adr/0085-generate-modules-in-the-build-with-setup-hooks.md)).
The build then needs no `peg-hs` executable.
The two ways differ in what the repository has:

- **Committing the module**: the repository has the generated module, and its diff can be reviewed. Any build tool can build the package, and `peg-hs` is needed only to generate the module again.
- **Generating in the build**: the repository has the grammar only, and the build generates the module again when the grammar changes. It needs `build-type: Hooks` of Cabal 3.14 or later.

The `.cabal` file of the package sets `build-type: Hooks`, and names peg-hooks in `custom-setup`.
The generated module goes in `autogen-modules`, as well as in `other-modules` or `exposed-modules`.

```cabal
cabal-version:      3.14
name:               calc
version:            0.1.0.0
build-type:         Hooks
extra-source-files: grammar/Calc.hpeg

custom-setup
  setup-depends:
    , base
    , Cabal-hooks  >=3.14 && <3.17
    , peg-hooks    >=0.1  && <0.2

executable calc
  main-is:          Main.hs
  hs-source-dirs:   src
  other-modules:    Calc.Parser
  autogen-modules:  Calc.Parser
  build-depends:
    , base
    , peg-runtime  >=0.1 && <0.2
    , text
  default-language: GHC2021
```

`SetupHooks.hs`, next to the `.cabal` file, gives each grammar with the name of its module.
The name must be the one of `%module` in the grammar; otherwise the build stops with an error at `%module`.
To use other hooks too, join them with `<>`.

```haskell
module SetupHooks (setupHooks) where

import Distribution.Simple.SetupHooks (SetupHooks)
import Peg.Hooks (Grammar (..), pegSetupHooks)

setupHooks :: SetupHooks
setupHooks = pegSetupHooks [Grammar "grammar/Calc.hpeg" "Calc.Parser"]
```

cabal builds a setup script of its own for `build-type: Hooks`, but `cabal check` wants a `Setup.hs`.
Put the same one as cabal's.

```haskell
module Main (main) where

import Distribution.Simple (defaultMainWithSetupHooks)
import SetupHooks (setupHooks)

main :: IO ()
main = defaultMainWithSetupHooks setupHooks
```

`cabal.project` points at peg-hooks and the packages it depends on, peg-codegen and peg-grammar, as well as peg-runtime.
peg-hooks is in the releases after v0.1.0-rc6.

```cabal
packages: .

source-repository-package
  type:     git
  location: https://github.com/tett23/peg-hs
  tag:      v0.1.0-rc7
  subdir:   packages/peg-runtime packages/peg-grammar packages/peg-codegen packages/peg-hooks
```

Before each component is built, a rule of peg-hooks reads the grammar, checks it as `peg-hs gen` does, and writes the module to the autogen directory of the component.
An error in the grammar stops the build, as `grammar/Calc.hpeg:20:28: error: ...`, and GHC reports a type error of an action at the line of the grammar.
The warnings about labels are shown and do not stop the build; there are no options such as `--Werror` or `--export`.

The grammar must be in `extra-source-files`.
cabal does not see a change of a file that is not listed there, and keeps building the old module.
The first build takes some minutes more: GHC 9.10 comes with Cabal 3.12, so cabal builds Cabal for the setup script.
[examples/hooks](examples/hooks) is a package that generates its parser in this way, and CI builds it.

## Commands

`peg-hs` has a subcommand for each purpose ([ADR 0037](docs/adr/0037-cli-subcommands.md)).
`peg-hs help COMMAND` shows the options and examples of a command.
An option that takes a value takes it as `--output FILE` or as `--output=FILE`.
Files are read and written as UTF-8, whatever the locale ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).

| Command | Purpose |
|---|---|
| `peg-hs gen GRAMMAR.hpeg [-o FILE]` | generate a Haskell module from a grammar |
| `peg-hs fmt [FILE\|DIR...]` | format grammars in one style |
| `peg-hs lint [FILE\|DIR...]` | warn of what is a mistake in grammars, and note what can be simpler |
| `peg-hs label GRAMMAR.hpeg [--write]` | insert labels where they are shown to be safe |
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

With `--export NAME`, the module exports only the names given, together with the names of `%export` ([ADR 0061](docs/adr/0061-select-generated-exports.md)).
`NAME` is an entry point (`parse`, `parseExpr`, `parseSyntaxRecover` and so on) or a name of `%syntax` (`nameOfSyntaxKind`, a syntax kind, a wrapper type without `(..)`, a cast or an accessor), and the option can be given more than once.
The module leaves out the rules and other declarations that only the other names use.
The blocks of `%{ }%` are always kept, so a name of the generator that they refer to must be given to `--export` too.
When declarations are left out, imports and functions of `%{ }%` that only their actions used become unused; the module then turns off the warnings of unused imports and top-level bindings. Generate without `--export` to see those warnings of the grammar's own code ([ADR 0062](docs/adr/0062-warnings-of-pruned-generated-modules.md)).
A name that the generator does not define is an error of the grammar, reported at line 1, column 1.

```sh
peg-hs gen grammar/Doc.hpeg --export parseSyntaxRecover --export nameOfSyntaxKind -o src/Doc/Parser.hs
```

A grammar is code: the Haskell of its blocks, actions and predicates runs with your rights when the generated module is compiled and used, so generate only grammars you trust as you would trust their Haskell.
Values outside those blocks go into the module too: the value of `%module`, the items of `%export` and the names of the grammar file and of the output.
peg-hs checks them and rejects values that would read as Haskell declarations ([ADR 0080](docs/adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).
`%module` takes a module name (`A.B.C`), and `%export` takes items of an export list: a name that may be qualified (`evalExpr`, `Expr`, `M.f`), a type name with `(..)` or with names and operators in parentheses (`Expr(..)`, `Expr(Add, Mul)`), an operator in parentheses (`(+++)`), any of these after `type` or `pattern` (`type (:+)`, `pattern P`), and `module` with a module name (`module Data.Text`).
An item outside these forms, such as one with `--`, `{-` or `where`, is an error at the item.
A file name with a control character (U+0000 to U+001F, or U+007F), such as a newline, is an error at line 1, column 1, and nothing is written.

### fmt

`fmt` formats grammars in place, in one fixed style ([ADR 0032](docs/adr/0032-grammar-formatter.md)).
No option chooses the style. Comments are kept.
`--check` writes nothing; it lists the files that are not formatted, and fails if there are any. It is for checks in CI.

A directory among the arguments stands for the `.hpeg` files under it.
Files with the old extension `.peg` are not looked for, since other PEG tools use it too; a file given by name is taken whatever its extension ([ADR 0050](docs/adr/0050-hpeg-extension.md)).
Without arguments, `fmt` takes every `.hpeg` file under the current directory.
Either way, directories whose name starts with `.` and `dist-newstyle` are skipped.
The search does not follow symbolic links, to files or to directories, so it stays inside the directory it starts from and ends on cyclic links ([ADR 0077](docs/adr/0077-fixes-of-the-security-audit.md)).
A file given by name is read and written through its link, and a directory given by name is searched even if it is a link, but the links inside it are skipped.
To format a grammar placed by a link, name it.

### lint

`lint` warns of what is a mistake in grammars that pass the static checks ([ADR 0033](docs/adr/0033-grammar-linter.md)):
alternatives that are never tried or never succeed, alternatives that are the same as an earlier one, labels without effect inside a lookahead, and bindings that are not used.
The rules are fixed, and no warning can be silenced: every warning goes away by fixing the grammar, and any warning makes `lint` fail.
Besides warnings, `lint` gives infos of what is not a mistake but can be simpler.
Infos are shown only with `--verbose`, written with `info:` in place of `warning:`, and never make `lint` fail ([ADR 0067](docs/adr/0067-lint-info-with-verbose.md)).
`omittable-unit-action` points at a `{ () }` that can be omitted: in a rule of type `()`, an alternative without a value other than unit may omit its action, and its value is `()` ([ADR 0063](docs/adr/0063-omit-unit-actions.md), [ADR 0064](docs/adr/0064-unit-rules-always-return-unit.md)).
`omittable-identity-action` points at an action that only returns a binding, as in `'(' e:Expr ')' { e }`, where the alternative returns the same value without the binding and the action; it is not given in grammars with `%syntax`, where a binding also names an accessor of the syntax tree ([ADR 0065](docs/adr/0065-omittable-identity-actions.md)).
`omittable-unit-annotation` points at a type annotation `A :: ()`, which a rule without a type annotation has anyway; it is not given for rules with parameters and templates ([ADR 0066](docs/adr/0066-omit-unit-type-annotations.md)).
The language server reports infos with the severity Hint, which most editors show faintly.
It chooses files as `fmt` does, and its search does not follow symbolic links either ([ADR 0077](docs/adr/0077-fixes-of-the-security-audit.md)).

### label

`label` finds the positions where the label check shows that a label cannot reject valid input, and lists the labels there as `FILE:LINE:COLUMN: ^NAME` ([ADR 0054](docs/adr/0054-automatic-label-insertion.md)).
With `--write`, it also writes them in the grammar, keeping comments and spaces.
The labels do not change the language, and they do not recover: the author writes `%recover` and a recovery rule for the labels to recover from (a code action of the language server adds a skeleton).

- A label is named `RULE_TARGET`: the rule referred to, the text of a literal of identifier characters, or the name of a literal of one symbol (such as `rparen`). `peg-hs help label` shows the table
- `--rule RULE` inserts only in that rule. It can be given more than once
- Nothing is inserted inside a label with a recovery rule, or in the rules it calls
- Near rules that test characters with semantic predicates, and in left recursion, the check cannot show labels to be safe, and none is inserted. The Lua grammar, for one, gets no label

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
When changes arrive faster than it checks them, it checks only the last version and sends its diagnostics ([ADR 0070](docs/adr/0070-faster-checks-in-the-language-server.md)).
Editors send only the changed parts of a document, and the server parses again only the top-level items that changed ([ADR 0071](docs/adr/0071-incremental-parsing-in-the-language-server.md)).
A message whose JSON nests arrays and objects deeper than 256 levels is answered with the parse error -32700, and the server goes on with the next message ([ADR 0080](docs/adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).

## Editors

An editor gets four tools for grammars: the language server, lint, formatting and syntax highlighting.
The settings below set up all four, and format a grammar on every save by default, since `fmt` has only one style ([ADR 0069](docs/adr/0069-richer-highlighting-and-format-on-save.md)).

`editors/` has grammars for syntax highlighting and a VS Code extension ([ADR 0034](docs/adr/0034-syntax-highlighting.md)).
The TextMate and tree-sitter grammars are also in the releases: `peg-hs-editors-<version>.tar.gz` on [Releases](https://github.com/tett23/peg-hs/releases), and `editors/` in the archive of the executable. The tree-sitter grammar there has its generated parser, so Neovim and Helix build it without the tree-sitter CLI. In the settings below, `/path/to/peg-hs/editors/tree-sitter-hpeg` can be the `tree-sitter-hpeg/` of an extracted archive ([ADR 0073](docs/adr/0073-editor-grammars-in-releases.md)).
Besides rules, literals and operators, they color brackets, the braces of actions, the delimiters of bindings and template arguments, and the arguments of directives by what they name: a rule, a label, the module or an extension ([ADR 0069](docs/adr/0069-richer-highlighting-and-format-on-save.md)).
Constructor names (`@Add`) and the classes of `%deriving` are colored as constructors and types ([ADR 0075](docs/adr/0075-generated-types-for-rules-without-actions.md)).
The Haskell of a grammar (verbatim blocks, types, actions, semantic predicates, arguments) is highlighted by the editor's Haskell grammar.
The tree-sitter grammar also has queries for folds, indents and locals: a rule folds with its type annotation, and an alternative on a new line is indented to the `<-` of its definition, as `fmt` lays it out.

The language server `peg-hs lsp` reports the errors and warnings of `gen` and `lint` as a grammar is edited, and formats it with `fmt`.
It also provides semantic tokens, go to definition, find references, hover and document symbols.
Its semantic tokens tell the rules, labels and the module in the arguments of directives apart, and the constructor names and the classes of `%deriving`.
Its hover shows the type of a rule, including the type inferred or the declaration of the type generated for a rule without a type annotation, and the type of a constructor.
Its code actions add the labels of `label`, and add `%recover` with a skeleton of a recovery rule to a label without one ([ADR 0054](docs/adr/0054-automatic-label-insertion.md)).
Another code action writes out the default constructor names of a rule as `@Name`, so that they stay when the alternatives change ([ADR 0075](docs/adr/0075-generated-types-for-rules-without-actions.md)).
The skeleton's value is the typed hole `{ _ }`: GHC shows its type, and the author writes the value.

None of the settings below has been checked by hand in the editor yet (**unchecked**).
The results of checks go to `docs/editors/`, and an editor loses this mark when its check is recorded ([ADR 0044](docs/adr/0044-release-v0-1-0.md)).

### VS Code (unchecked)

`editors/vscode` is an extension with the TextMate grammar (`editors/textmate/hpeg.tmLanguage.json`) that starts the language server.
It is not on the Marketplace yet, so install it from the repository: install its dependencies, link it into the directory of extensions, and restart VS Code.
If `peg-hs` is not on `PATH`, the setting `peg-hs.path` points at the executable.
Write `peg-hs.path` in your user settings: it has the scope `machine`, so the settings of a workspace (`.vscode/settings.json`) cannot change it, and a repository cannot make VS Code run an executable of its choosing ([ADR 0080](docs/adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).
The extension works in an untrusted workspace too (Restricted Mode), with the `peg-hs.path` of your user settings, since the language server only reads grammars and does not run their Haskell.
The extension turns on `editor.formatOnSave` for the language `hpeg`, so a grammar is formatted on every save.
To turn it off, set `"[hpeg]": { "editor.formatOnSave": false }` in your settings.

```sh
(cd editors/vscode && npm ci)
ln -s "$PWD/editors/vscode" ~/.vscode/extensions/peg-hs
```

`editors/vscode/package.json` overrides the version of minimatch, a dependency of vscode-languageclient, with `^11.0.1`, which fixes the denial of service [GHSA-g3hv-75wg-m249](https://github.com/advisories/GHSA-g3hv-75wg-m249); vscode-languageclient itself still asks for `^10.2.6` ([ADR 0077](docs/adr/0077-fixes-of-the-security-audit.md)).
minimatch 11 removed `makeRe()`, which vscode-languageclient calls only when the language server sends glob patterns: for file operations, diagnostic filters or notebook documents.
`peg-hs lsp` declares none of these, and a test of peg-lsp fails if it starts to.
The override goes away when vscode-languageclient accepts a fixed minimatch.

### Neovim (unchecked)

Put `peg-hs` on `PATH` first ([Installation](#installation)); the language server and the linter run it.
Then register the file type:

```lua
vim.filetype.add({ extension = { hpeg = 'hpeg' } })
```

#### Language server

The language server is set up with `vim.lsp.config` of Neovim 0.11 or later; no plugin is needed.
The autocommand formats a grammar with `fmt` on every save.

```lua
vim.lsp.config('peg_hs', { cmd = { 'peg-hs', 'lsp' }, filetypes = { 'hpeg' }, root_markers = { '.git' } })
vim.lsp.enable('peg_hs')
vim.api.nvim_create_autocmd('BufWritePre', { pattern = '*.hpeg', callback = function() vim.lsp.buf.format() end })
```

As a grammar is edited, it reports the errors of `gen` as errors, the warnings of `lint` as warnings, and the infos of `lint` as hints, which Neovim shows faintly.
`vim.lsp.buf.format()` also formats it at any time.

#### Lint without the language server

To run `peg-hs lint` without the language server, register it with [nvim-lint](https://github.com/mfussenegger/nvim-lint).
`peg-hs lint` reads the file from disk, so it runs on opening and saving the file, and on leaving insert mode.
It is given `--verbose` so that the infos are shown too; leave it out to see only errors and warnings.

```lua
local lint = require('lint')
lint.linters.peg_hs = {
  cmd = 'peg-hs',
  args = { 'lint', '--verbose' },
  stdin = false,
  append_fname = true,
  stream = 'stderr',
  ignore_exitcode = true,
  parser = require('lint.parser').from_errorformat(
    '%f:%l:%c: %trror: %m,%f:%l:%c: %tarning: %m,%f:%l:%c: %tnfo: %m',
    { source = 'peg-hs' }
  ),
}
lint.linters_by_ft.hpeg = { 'peg_hs' }
vim.api.nvim_create_autocmd('FileType', { pattern = 'hpeg', callback = function() lint.try_lint() end })
vim.api.nvim_create_autocmd({ 'BufWritePost', 'InsertLeave' }, { pattern = '*.hpeg', callback = function() lint.try_lint() end })
```

Use either the language server or nvim-lint: both report the same warnings, so with both they appear twice.

#### Highlighting

For highlighting, register the tree-sitter grammar `editors/tree-sitter-hpeg` with nvim-treesitter (the main branch).
A `User TSUpdate` autocommand gives the place of the grammar and its directory of queries; then run `:TSInstall hpeg` in Neovim.
Building the grammar needs the tree-sitter CLI.
nvim-treesitter does not turn highlighting on by itself, so a `FileType` autocommand calls `vim.treesitter.start()`.
The same autocommand sets the folds of Neovim and the indents of nvim-treesitter from the queries.

The grammar can be installed from GitHub, without a clone ([ADR 0074](docs/adr/0074-neovim-tree-sitter-from-github.md)).
It installs the grammar of the release tag in `revision`.
With the tag of the same version as the language server (`peg-hs lsp`), highlighting and diagnostics follow the same version of the notation.
With `revision`, `:TSUpdate` does not install it again until the tag changes.
Without `revision`, it installs the head of main, and `:TSUpdate` installs it again every time.
With `url`, `queries` is a path from the root of the repository, not from `location`.

```lua
vim.api.nvim_create_autocmd('User', { pattern = 'TSUpdate', callback = function()
  require('nvim-treesitter.parsers').hpeg = { install_info = {
    url = 'https://github.com/tett23/peg-hs',
    location = 'editors/tree-sitter-hpeg',
    queries = 'editors/tree-sitter-hpeg/queries',
    revision = 'v0.1.0-rc4',
  } }
end })
vim.api.nvim_create_autocmd('FileType', { pattern = 'hpeg', callback = function()
  vim.treesitter.start()
  vim.wo.foldmethod = 'expr'
  vim.wo.foldexpr = 'v:lua.vim.treesitter.foldexpr()'
  vim.bo.indentexpr = "v:lua.require'nvim-treesitter'.indentexpr()"
end })
```

To install it from a clone, or from an extracted archive of a release ([Installation](#installation)), register it in the `TSUpdate` autocommand above with `path` instead:
With `path`, `queries` is a path from `path`.

```lua
require('nvim-treesitter.parsers').hpeg = {
  install_info = { path = '/path/to/peg-hs/editors/tree-sitter-hpeg', queries = 'queries' },
}
```

To highlight the Haskell fragments, such as actions and verbatim blocks, install the haskell parser too (`:TSInstall haskell`).
Without it, the Haskell fragments are not highlighted.

With the old version of nvim-treesitter (the master branch), register it with `get_parser_configs()`.
The grammar has an external scanner (`src/scanner.c`), so `files` lists two files; copy the queries to `queries/hpeg/` on the runtime path.

```lua
require('nvim-treesitter.parsers').get_parser_configs().hpeg = {
  install_info = { url = '/path/to/peg-hs/editors/tree-sitter-hpeg', files = { 'src/parser.c', 'src/scanner.c' } },
  filetype = 'hpeg',
}
```

### Helix (unchecked)

Add the language, the grammar and the language server to `languages.toml`, and run `hx --grammar build`.
Copy the queries `highlights.scm`, `injections.scm` and `locals.scm` to `runtime/queries/hpeg/`; `folds.scm` and `indents.scm` are written for Neovim.
With `auto-format = true`, Helix formats a grammar with the language server on every save.
Formatting on save is one of the things to check by hand in Helix ([ADR 0044](docs/adr/0044-release-v0-1-0.md)).

```toml
[[language]]
name = "hpeg"
scope = "source.hpeg"
file-types = ["hpeg"]
comment-token = "#"
language-servers = ["peg-hs"]
auto-format = true

[[grammar]]
name = "hpeg"
source = { path = "/path/to/peg-hs/editors/tree-sitter-hpeg" }

[language-server.peg-hs]
command = "peg-hs"
args = ["lsp"]
```

## WebAssembly

Every release has `peg-hs.wasm`, a WASI preview1 reactor that analyses, generates and formats grammars in a browser or in Deno ([ADR 0078](docs/adr/0078-grammar-analysis-in-wasm.md)).
The name has no version; the tag of the release tells the version, and `SHA256SUMS` of the same release has its checksum.
It does what `peg-hs gen` and `peg-hs fmt` do with a grammar given as text: it does not parse inputs with the grammar, which needs GHC to compile the generated module.
`scripts/build-wasm.sh` builds it with the toolchain of [ghc-wasm-meta](https://gitlab.haskell.org/haskell-wasm/ghc-wasm-meta) at a fixed commit, which `nix shell` provides:

```sh
nix shell "gitlab:haskell-wasm/ghc-wasm-meta/8079eb96bbc63823d99ad8acaff0765532625474?host=gitlab.haskell.org#all_9_10" \
  -c scripts/build-wasm.sh peg-hs.wasm
```

### Exports

| Name | Type | Use |
| --- | --- | --- |
| `memory` | memory | The linear memory |
| `_initialize` | `() -> ()` | Initialises the reactor; call it once, first |
| `hs_init` | `(i32, i32) -> ()` | Initialises the Haskell runtime; call `hs_init(0, 0)` once, after `_initialize` |
| `malloc` | `(i32) -> i32` | Allocates linear memory |
| `free` | `(i32) -> ()` | Frees a block of `malloc`, or one that `analyze` or `format` returned |
| `analyze` | `(i32, i32) -> i32` | Analyses a grammar and generates its module |
| `format` | `(i32, i32) -> i32` | Formats a grammar |

`analyze` and `format` take the address and the length in bytes of a request: JSON in UTF-8.
They return the address of a new block, whose first 4 bytes are the length in bytes of the response (an unsigned little-endian integer), followed by the response, JSON in UTF-8.
The request is copied before the function returns, so it can be freed then; free the response after reading it.
An exception in Haskell does not stop the wasm: the response is `{"error": "internal error: ..."}`.
A length that is negative, or that reaches past the end of the linear memory from the address, is not read: the response is `{"error": "the request is outside the memory"}` ([ADR 0080](docs/adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).

```js
const { instance } = await WebAssembly.instantiateStreaming(fetch("peg-hs.wasm"), { wasi_snapshot_preview1: wasi });
const ex = instance.exports;
ex._initialize();
ex.hs_init(0, 0);

const call = (name, request) => {
  const bytes = new TextEncoder().encode(JSON.stringify(request));
  const p = ex.malloc(bytes.length);
  new Uint8Array(ex.memory.buffer, p, bytes.length).set(bytes);
  const r = ex[name](p, bytes.length);
  ex.free(p);
  const n = new DataView(ex.memory.buffer).getUint32(r, true);
  const response = JSON.parse(new TextDecoder().decode(new Uint8Array(ex.memory.buffer, r + 4, n)));
  ex.free(r);
  return response;
};
call("analyze", { grammar: "%module Calc\n..." });
```

### Requests and responses

The request of `analyze`:

```json
{"grammar": "%module Calc\n...", "sourceName": "Calc.hpeg", "outputName": "Calc.hs", "debugEntry": false}
```

- `grammar` (required): the text of the grammar.
- `sourceName` (default `Grammar.hpeg`): the name of the grammar file that the `LINE` pragmas name, the path given to `peg-hs gen`.
- `outputName` (default `sourceName` with the extension `.hs`): the name of the generated file, the `-o` of `gen`.
- `debugEntry` (default `false`): the `--debug-entry` of `gen`.

The response:

```json
{
  "diagnostics": [{"severity": "error", "line": 3, "column": 7, "message": "undefined rule Term"}],
  "ast": {"kind": "Grammar", "line": 1, "column": 1, "text": null, "children": []},
  "types": "data Expr = Add Expr Term | Expr2 Term\n  deriving (Eq, Show)",
  "module": null
}
```

- `diagnostics`: the errors and warnings, with `severity` `"error"` or `"warning"`. `line` and `column` start at 1, and a column counts code points (a tab is one), as `peg-hs` writes them. `message` is what `peg-hs gen` writes after `file:line:column: error: `. The warnings are those of the labels that `gen` reports; the warnings of `peg-hs lint` are not there.
- `ast`: the syntax tree of the grammar as written, before the templates are expanded, or `null` when the grammar does not parse.
- `types`: the declarations of the generated types ([ADR 0075](docs/adr/0075-generated-types-for-rules-without-actions.md)) in the order of their rules, separated by blank lines; the empty string when the grammar has none, and `null` when its templates do not expand. It is there even when the checks find errors.
- `module`: the generated module, byte for byte the file that `peg-hs gen` writes for the same request, or `null` when there are errors.

The request of `format` is `{"grammar": "..."}`, and its response is `{"text": "...", "diagnostics": [...]}`.
`text` is what `peg-hs fmt` writes, or `null` with errors in `diagnostics`.
A request that is not JSON or not UTF-8, has no `grammar`, or has a member of another type gets `{"error": "..."}` only.
JSON whose arrays and objects nest deeper than 256 levels is not taken as JSON ([ADR 0080](docs/adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).

### The syntax tree

Every node of `ast` has the same shape, for a tree view:

```json
{"kind": "Rule", "line": 5, "column": 1, "text": "Expr", "children": [...]}
```

`line` and `column` are `null` for the nodes whose location the syntax tree does not keep (most expressions); use the location of the nearest ancestor.
`text` is `null` for the nodes without one.

| `kind` | `text` | Location | `children` |
| --- | --- | --- | --- |
| `Grammar` | `null` | 1:1 | The directives, `Verbatim` and the rules, in the order of their locations |
| `Directive` | The name of the directive, such as `%module` | The directive | `Value`s (one for each name of `%export`, `%language`, `%deriving` and `%recover`; none for `%syntax`) |
| `Verbatim` | The Haskell code of `%{ ... }%` | The code | none |
| `Value` | The value of a directive | The value | none |
| `Rule` | The name of the rule | The definition | `Parameter`, `TemplateParameter`, `Type`, `Alternative` |
| `Parameter` | `name :: Type` | The type | none |
| `TemplateParameter` | `name`, or `name :: a` with a type | `null` | none |
| `Type` | The type of a type annotation (only for rules with one) | The type | none |
| `Alternative` | `null` | The alternative | `Item`, `Action` and `Constructor`, in the order of their locations |
| `Action` | The Haskell code | The code | none |
| `Constructor` | The name after `@` | The name | none |
| `Item` | The name of the binding, or `null` | The element | One expression |
| `Literal` | The literal as written | `null` | none |
| `Class` | The character class as written | `null` | none |
| `Any` | `.` | `null` | none |
| `Reference` | The name of the rule | The reference | `Argument`s |
| `Argument` | The Haskell code of an argument | The argument | none |
| `Group` | `null` | `null` | `Sequence`s |
| `Sequence` | `null` | `null` | `Item`s |
| `Star`, `Plus`, `Optional`, `And`, `Not`, `Capture`, `Discard` | `null` | `null` | One expression |
| `Label` | The label | The label | One expression |
| `AndPredicate`, `NotPredicate` | The Haskell code | The code | none |
| `Template` | The name of the template | The call | The expressions of the arguments, then `Argument`s |

`Discard` does not appear in a grammar as written; it is in the table to cover every constructor of the expressions.

### Imports

The wasm imports only these functions of `wasi_snapshot_preview1`, and nothing of other modules:
`args_get`, `args_sizes_get`, `environ_get`, `environ_sizes_get`, `clock_time_get`, `clock_res_get`, `random_get`, `fd_write` (standard output and standard error only) and `proc_exit`.
The build now imports `environ_get`, `environ_sizes_get`, `clock_time_get`, `fd_write` and `proc_exit` of them.
The runtime of GHC and the C library also import 13 functions of files and polling, which none of the calls measured in [ADR 0079](docs/adr/0079-stub-wasi-imports-outside-the-contract.md) used.
`scripts/build-wasm.sh` replaces them with functions in the wasm (`wasm/stubs.wat`) that read no argument and return an error at once, so that a WASI with only the functions above loads it ([ADR 0079](docs/adr/0079-stub-wasi-imports-outside-the-contract.md)):

| Function | Returns |
| --- | --- |
| `fd_prestat_get` | `8` (`EBADF`): no directory is preopened |
| `fd_close`, `fd_fdstat_get`, `fd_fdstat_set_flags`, `fd_filestat_get`, `fd_filestat_set_size`, `fd_prestat_dir_name`, `fd_read`, `fd_seek`, `path_create_directory`, `path_filestat_get`, `path_open`, `poll_oneoff` | `52` (`ENOSYS`) |

## Migrating from the extension .peg

Grammar files were `.peg` until v0.1.0-rc1; they are `.hpeg` now, and the language of the editors is `hpeg` ([ADR 0050](docs/adr/0050-hpeg-extension.md)).

1. Rename the grammars: `git mv Grammar.peg Grammar.hpeg`.
2. Generate the modules again with the new paths, since a generated module records the path of its grammar.
3. Change the editor settings: the language and file type `peg` becomes `hpeg`, the tree-sitter grammar is `editors/tree-sitter-hpeg`, and the queries go to `queries/hpeg/`.

## Known limitations

- **Distribution**: executables are for Linux (x86-64) and macOS (arm64) only. On Windows, build from source. The packages are not on Hackage yet ([ADR 0044](docs/adr/0044-release-v0-1-0.md)).
- **Versions of GHC**: the packages and generated modules support GHC 9.10, 9.12 and 9.14. CI checks only 9.10, the version ghcup recommends; 9.12 and 9.14 were checked up to v0.1.0-rc2 ([ADR 0057](docs/adr/0057-recommended-ghc-only.md)). GHC 9.8 and earlier are not supported ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).
- **Encoding**: grammars and inputs must be UTF-8. Convert files in other encodings first ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).
- **`peg-hs parse` and `%env`**: `parse` cannot handle grammars with `%env` (the read-only parse environment), since it has no way to give the value of the environment. Check such grammars by calling the generated module from a program ([ADR 0036](docs/adr/0036-parse-command.md)).
- **GHC for `peg-hs parse`**: `parse` compiles the parser with the `ghc` on `PATH`, which must be GHC 9.10, 9.12 or 9.14 ([ADR 0036](docs/adr/0036-parse-command.md), [ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).
- **Rules whose type names collide**: with `%syntax`, each rule has a type named after it, so two rules such as `expr` and `Expr` are an error. `peg-hs parse` always generates the syntax tree too, so it rejects such grammars even without `%syntax` ([ADR 0053](docs/adr/0053-type-names-of-rules-without-case.md)).
- **The check of labels is conservative**: it does not miss labels that may reject valid input, and in exchange it may warn of labels that are in fact safe. `%safe` silences the warning of a label that the author checked. The grammar of the notation itself has 23 `%safe` ([ADR 0028](docs/adr/0028-label-safety-check.md), [ADR 0038](docs/adr/0038-label-check-precision-and-strip-labels-entries.md)).
- **Rule templates**: the arguments of a template may use the parameters of the caller, but not its bindings; pass the value of a binding as a value argument. A template cannot be a rule of `%entry`, `%start` or `%recover` ([ADR 0031](docs/adr/0031-rule-templates.md), [ADR 0055](docs/adr/0055-templates-and-parameterized-rules-in-stages.md)).
- **The nesting of expressions**: an expression nests at most 256 levels deep. Each group, prefix and postfix operator, label and template call is a level, and a deeper expression is an error at the level that goes over the limit. The limit cannot be changed ([ADR 0080](docs/adr/0080-fixes-of-the-security-audit-of-2026-11-07.md)).
- **The tree-sitter grammar**: an alternative with neither elements nor an action (`S <- 'a' /`) is an error. Such an alternative has no value, so `peg-hs gen` always rejects it too, and no valid grammar is shown as an error ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).
- **The TextMate grammar**: its rules are regular expressions, so distinctions that depend on the context (the call `A(x)` and the sequence `A (x)`) are approximate. The semantic tokens of the language server distinguish them exactly ([ADR 0034](docs/adr/0034-syntax-highlighting.md)).
- **Editor settings**: the settings of the three editors above are not checked by hand yet ([ADR 0044](docs/adr/0044-release-v0-1-0.md)). The VS Code extension is not on the Marketplace.

## Documents

- [docs/syntax.en.md](docs/syntax.en.md): the `.hpeg` notation, with examples
- [docs/specifications.md](docs/specifications.md): the specification of the product (in Japanese)
- [docs/adr/](docs/adr/): the records of design decisions (ADRs), in Japanese. Each item of the specification can be traced to its decision.
- [CONTRIBUTING.md](CONTRIBUTING.md): the development environment, tests, regenerating generated files, ADRs, commits and the release procedure
- `CHANGELOG.md` of each package: the changes of each version

## License

[MIT](LICENSE).
The test data under `conformance/data/` follows the LICENSE in each of its directories.
