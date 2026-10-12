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
peg-hs Grammar.peg -o Grammar.hs
```

Without installing, run it through cabal instead:

```sh
cabal run peg-hs -- Grammar.peg -o Grammar.hs
```

The generated module depends only on the `peg-runtime` package and exports `parse :: Text -> Either ParseError a` for the start rule.

The generator warns about labels that may make the grammar reject valid input ([ADR 0028](docs/adr/0028-label-safety-check.md)). `--Werror` makes a warning fail the generation, and `%safe label` in the grammar silences the warning for a label checked by hand.

## Development

See [CONTRIBUTING.md](CONTRIBUTING.md) for how changes are made: ADRs, tests first, commits and releases.

The toolchain is the one ghcup marks as recommended: GHC 9.10.3, cabal-install 3.16.1.0, and HLS 2.14.0.0.
`cabal.project` pins the compiler version.
If you use [mise](https://mise.jdx.dev/), the bundled `mise.toml` puts ghcup's binaries on the project's `PATH`.

```sh
ghcup install ghc 9.10.3
ghcup install cabal 3.16.1.0
```

After cloning, enable the git hooks.
Committed ADRs are immutable: [adr-guard](https://github.com/tett23/adr-guard) rejects changes to them in the pre-commit hook and in CI.

```sh
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

The golden data of the Lua test is made with the reference implementation, Lua 5.5.1, which is needed only to regenerate it:

```sh
conformance/lua/golden/regen.sh
```

## License

[MIT](LICENSE)
