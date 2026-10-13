# Contributing to peg-hs

This document describes how peg-hs is developed.
The Japanese version ([CONTRIBUTING.ja.md](CONTRIBUTING.ja.md)) is canonical.
This English version is a translation; where the two differ, the Japanese version applies.

## How changes are made

Changes to peg-hs start from an ADR (Architecture Decision Record), which records a design decision.
ADRs live in `docs/adr/`.

### Writing an ADR

- Write an ADR before implementing. Features and specification changes without an ADR are not accepted
- Name the file `NNNN-kebab-case.md`, where `NNNN` is the next number after the existing ADRs and the rest is an English name that tells what it is about
- Set the status to 提案 (proposed)
- Include the following sections. Add a section for changes to data structures or algorithms, and for anything worth keeping as a record of the discussion

```
# ADR NNNN: Title

ステータス: 提案

## 文脈 (context)

## 実装すること (what to implement)

## 実装しないこと (what not to implement)

## テスト設計 (test design)

## トレードオフ (trade-offs)
```

- State in a section 実装の段階 (implementation stage) where the ADR fits in the implementation order of [ADR 0013](docs/adr/0013-roadmap-toolchain-memo.md)

### Review and adoption

- Do not commit a new ADR; it is reviewed first
- Once adopted, set its status to 採択 (adopted) and commit it
- When adopting an ADR that changes the notation, update `docs/syntax.md` in the same commit and add the ADR to the list of reflected ADRs at its top
- When an ADR changes the specification, update `docs/specifications.md` and the README (both the English and the Japanese version) at the same time. These three must always be up to date on main

### Committed ADRs do not change

- A committed ADR cannot be changed, except for its status line. [adr-guard](https://github.com/tett23/adr-guard) checks this in the pre-commit hook and in CI
- To change a decision, write a new ADR with the change. Rewrite the status line of the original ADR as 採択→(the changed part)は ADR NNNN
- To discard an ADR, set its status to 破棄 (discarded) and write the reason in `docs/specifications.md`
- When an implementation could not follow its ADR, or took a different form, write an ADR that records it (for example [ADR 0015](docs/adr/0015-implementation-deviations.md), [ADR 0025](docs/adr/0025-lua-toml-implementation-deviations.md), [ADR 0029](docs/adr/0029-label-safety-implementation-deviations.md))

## Implementation

### Tests first

- Write the tests of the ADR's test design first, see them fail, then implement
- For a change that cannot be tested automatically (a setting, for example), write how to check it in the ADR's test design, and check it by running it after implementing
- Do not write tests without a bound on their running time. Write complexity checks with inputs small enough that a regression fails within seconds; an input that takes exponential time must show up as a failure, not as a test that never ends

### Generated code

- Generated modules (the codegen fixtures, the grammars of the conformance tests, the self-hosted parser, the label-free variants) are committed. The tests check that they match the generator's current output
- After changing the generator or a grammar, regenerate them with `scripts/regen-fixtures.sh`
- Grammars are committed formatted with `peg-hs fmt`; CI runs `peg-hs fmt --check` ([ADR 0032](docs/adr/0032-grammar-formatter.md))
- Grammars have no warnings of `peg-hs lint`, which CI runs ([ADR 0033](docs/adr/0033-grammar-linter.md))
- CI does not build or test a change of `docs/` and Markdown files only; adr-guard still checks it. A new push to a pull request stops the run of the previous push ([ADR 0039](docs/adr/0039-faster-ci.md))
- Test suites run their tests in parallel. Each test uses files and directories that no other test uses ([ADR 0039](docs/adr/0039-faster-ci.md))
- CI runs the test suites in three jobs (`test-grammar`, `test-conformance` and `test-packages`), one suite at a time in each. A new test suite goes to the job that keeps the three about the same length, from the latest CI timings in `docs/benchmarks/` ([ADR 0041](docs/adr/0041-split-test-jobs-and-cores.md))
- To add a construct to the notation and use it in the notation's own grammar (`packages/peg-grammar/grammar/Peg.peg`), regenerate twice ([ADR 0027](docs/adr/0027-switch-to-self-hosted-parser.md)): first add the rules that accept the construct without using it, and regenerate; then use it in `Peg.peg`, and regenerate with the new generator

### Performance

- For changes touching peg-runtime or peg-codegen, compare benchmark results before and after on the same machine ([ADR 0007](docs/adr/0007-performance-discipline.md))
- Measurements behind performance decisions go to `docs/benchmarks/` as snapshots

### Dependencies

- If something can be reimplemented easily and its license allows it, reimplement it instead of adding a dependency. When only part of it is needed, implementing that part is enough
- Give reimplemented code thorough tests, modelled on the tests of the original

### Data of the conformance tests

- Do not modify test data taken from elsewhere (`conformance/data/`). Record the version and the source in `SOURCE`, and the license in `LICENSE`
- Snapshots of conformance and measurements (`docs/conformance/`, `docs/benchmarks/`) do not change after they are committed. New results are added as new snapshots

## Development environment

The commands for the toolchain, running tests and benchmarks, and regenerating code are in the development section of the README ([README.md](README.md)).
Note the following:

- Use the compiler and build tool versions that ghcup marks as recommended ([ADR 0013](docs/adr/0013-roadmap-toolchain-memo.md)). ghcup's default `cabal` may have moved to a newer version, so it helps to name the version in commands, as in `cabal-3.16.1.0`
- After cloning, run `git config core.hooksPath .githooks` to enable the adr-guard hook

## Languages of the documents

- ADRs, the specification (`docs/specifications.md`) and the notation guide (`docs/syntax.md`) are written in Japanese
- Haddock of public modules is written in English
- Update both the English and the Japanese README
- Follow the style of [README.ja.md](README.ja.md) and the existing ADRs for Japanese documents

## Commits and branches

- Split commits by what they are about. An ADR, its implementation, tests and document updates are often separate commits
- Write commit subjects in Japanese in the form `type(scope): description`. The type is `feat`, `fix`, `test`, `docs`, `refactor` and so on, and the scope is a package name (`peg-runtime`, `peg-grammar` and so on). Mention the related ADR numbers in the subject
- Do not rebase main. The only exception is a secret, such as an API key, committed by mistake
- Branches may be rebased until they are merged. Always merge with `--no-ff`

## Releases

- Tags starting with `v` are releases. Tags of the form `v0.0.1-rc` are pre-releases
- Write release notes in GitHub Releases. Group the changes under headings such as Added, Changed, Removed and Fixed, and link each change to its commit or pull request where possible
- peg-hs is not yet published on Hackage ([ADR 0009](docs/adr/0009-hackage-publication.md))

## License

peg-hs is licensed under the MIT License.
Contributions are published under the MIT License.
