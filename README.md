# peg-hs

A PEG-to-Haskell parser generator with left recursion support.

[日本語版 README](README.ja.md)

- Accepts the full standard PEG syntax plus direct and indirect left recursion, based on bounded left recursion (Medeiros et al. 2014)
- Standalone code generator in the style of happy / alex: deterministically generates `.hs` from `.peg` (byte-identical output for identical input)
- Each rule carries a result type and semantic actions, so generated parsers return your AST directly
- Context-sensitive extensions (semantic predicates, parameterized rules, a read-only parse environment, and column references) for indentation-sensitive and forward-referencing syntax, designed so that packrat memoization and left recursion stay sound
- Type errors in semantic actions are reported at their line and column in the `.peg` file

**Status: design phase.** The specification and ADRs are complete; implementation has not started.

See [docs/specifications.md](docs/specifications.md) for the specification, [docs/syntax.md](docs/syntax.md) for the `.peg` notation with examples, and [docs/adr/](docs/adr/) for design decisions. These documents are currently written in Japanese.

## Development

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

Performance regressions are caught with local benchmarks.
For changes touching peg-runtime or peg-codegen, compare benchmark results before and after on the same machine (ADR 0007).

## License

[MIT](LICENSE)
