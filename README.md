# peg-hs

A PEG-to-Haskell parser generator with left recursion support.

[日本語版 README](README.ja.md)

- Accepts the full standard PEG syntax plus direct and indirect left recursion, based on bounded left recursion (Medeiros et al. 2014)
- Standalone code generator in the style of happy / alex: deterministically generates `.hs` from `.peg` (byte-identical output for identical input)
- Each rule carries a result type and semantic actions, so generated parsers return your AST directly

**Status: design phase.** The specification and ADRs are complete; implementation has not started.

See [docs/specifications.md](docs/specifications.md) for the specification and [docs/adr/](docs/adr/) for design decisions. These documents are currently written in Japanese.

## Development

After cloning, enable the git hooks.
Committed ADRs are immutable: [adr-guard](https://github.com/tett23/adr-guard) rejects changes to them in the pre-commit hook and in CI.

```sh
git config core.hooksPath .githooks
```

Performance regressions are caught with local benchmarks.
For changes touching peg-runtime or peg-codegen, compare benchmark results before and after on the same machine (ADR 0007).

## License

[MIT](LICENSE)
