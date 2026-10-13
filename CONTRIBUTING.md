# Contributing to peg-hs

This document describes how peg-hs is developed.
The Japanese version ([CONTRIBUTING.ja.md](CONTRIBUTING.ja.md)) is canonical.
This English version is a translation; where the two differ, the Japanese version applies.

The first release candidate of peg-hs, `v0.1.0-rc1`, is distributed through GitHub Releases.
peg-hs is not yet published on Hackage.
It will be published on Hackage with `v0.1.0` ([ADR 0044](docs/adr/0044-release-v0-1-0.md)).

## Development environment

Use the compiler and build tool versions that ghcup marks as recommended ([ADR 0013](docs/adr/0013-roadmap-toolchain-memo.md)).
They are currently GHC 9.10.3 and cabal-install 3.16.1.0.
`cabal.project` pins the compiler with `with-compiler: ghc-9.10.3`.

```sh
ghcup install ghc 9.10.3
ghcup install cabal 3.16.1.0
```

ghcup's default `cabal` may have moved to a newer version.
ghcup also installs an executable per version (`cabal-3.16.1.0`), so if the default has moved, read `cabal` in the commands of this document as `cabal-3.16.1.0`.
If you use [mise](https://mise.jdx.dev/), the repository's `mise.toml` puts ghcup's `~/.ghcup/bin` on the project's `PATH`.

The packages support GHC 9.10, 9.12 and 9.14 ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md)).
The `tested-with` field of each `.cabal` file lists the versions that were checked (9.10.3, 9.12.4 and 9.14.1).
For development, 9.10.3 alone is enough.
CI checks the build with 9.12 and 9.14.
To check it locally, install that GHC and name it, as in `cabal build -w ghc-9.14.1 all`.

After cloning, install [adr-guard](https://github.com/tett23/adr-guard) and enable the git hooks.
adr-guard is a tool that checks that committed ADRs and benchmark records have not changed (see "ADRs and adr-guard").

```sh
cargo install --git https://github.com/tett23/adr-guard --tag v0.8.1
git config core.hooksPath .githooks
```

`git config core.hooksPath .githooks` is needed in every clone.
Keep the version of adr-guard the same as the one in CI (`.github/workflows/adr.yml`) ([ADR 0047](docs/adr/0047-adr-guard-v0.8.1.md)).

The tests of the editor grammars (see "Tests of the editor grammars") need the LTS version of Node.

## Building and testing

To build every package and run every test, run the following at the root of the repository.

```sh
cabal build all
cabal test all
```

Test suites run their tests in parallel.
Each test therefore uses files and directories that no other test uses ([ADR 0039](docs/adr/0039-faster-ci.md)).

The slowest suite, peg-grammar-test, takes the option `--shard i/n` to run only the i-th of n parts ([ADR 0042](docs/adr/0042-shard-peg-grammar-test.md)).
CI uses it to split the suite into three jobs.

```sh
cabal test peg-grammar --test-options='--shard 1/3'
```

To keep the parts about the same length, a property test of 300 cases or more that takes 10 seconds or more in CI is split into several tests with `chunkedProperty` in `packages/peg-grammar/test/Shard.hs`.
A property left as one test would make only the part that contains it longer.

Some tests read files outside their package (the grammars of other packages, `editors/test` and so on).
A package unpacked from its source tarball (sdist) does not have those files.
These tests then do not fail; they skip and report the reason in a line starting with `skipped:` ([ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)).
The `sdist` jobs of CI count and print these lines.
A new test that reads outside its package skips in the same way.

Every exposed module of the four published libraries (peg-runtime, peg-grammar, peg-codegen and peg-lsp) is fully documented with Haddock ([ADR 0044](docs/adr/0044-release-v0-1-0.md)).
To run the check of CI locally, run the following.
It fails if a module is below 100% coverage.

```sh
cabal haddock peg-runtime peg-grammar peg-codegen peg-lsp 2>&1 | scripts/haddock-coverage.sh
```

The CommonMark conformance test takes options for inspecting its results.
`--show N` prints the input, the expected output and the actual output of example N, `--report FILE` writes the results per section as Markdown, and `--accept` records the examples that pass now.

```sh
cd conformance && $(cabal list-bin peg-conformance:test:commonmark-conformance) --show 5
```

## Regenerating generated files

Generated modules are committed to the repository.
They are the codegen fixtures, the parsers generated from the grammars of the conformance tests, the self-hosted parser of the notation, and the variants without labels.
The tests check that the committed files match the generator's current output.
After changing the generator or a grammar, regenerate them:

```sh
scripts/regen-fixtures.sh
```

If the default `cabal` has moved, name the `cabal` to use, as in `CABAL=cabal-3.16.1.0 scripts/regen-fixtures.sh`.
At the end, the script runs `scripts/embed-runtime.py`, which rewrites the sources of peg-runtime that `peg-hs parse` uses (`packages/peg-cli/app/Embedded.hs`) ([ADR 0036](docs/adr/0036-parse-command.md)).
Run the script also after changing the sources of peg-runtime.
If `Embedded.hs` is out of date, the tests of peg-cli fail.

The parser of the notation is generated from the notation's own grammar, `packages/peg-grammar/grammar/Peg.hpeg` ([ADR 0027](docs/adr/0027-switch-to-self-hosted-parser.md)).
To add a construct to the notation and use it in `Peg.hpeg` itself, regenerate twice.
The current generator cannot read the construct, so changing both at once leaves `Peg.hpeg` impossible to generate.

1. Add the rules that accept the construct to `Peg.hpeg` without using it, and regenerate with `scripts/regen-fixtures.sh`
2. Use the construct in `Peg.hpeg`, and run `scripts/regen-fixtures.sh` again with the new generator

Grammars of the repository are committed formatted with `peg-hs fmt` ([ADR 0032](docs/adr/0032-grammar-formatter.md)).
They have no warnings of `peg-hs lint` either ([ADR 0033](docs/adr/0033-grammar-linter.md)).
Without arguments, both take every `.hpeg` file under the current directory.
CI runs these two at the root of the repository:

```sh
$(cabal list-bin exe:peg-hs) fmt --check
$(cabal list-bin exe:peg-hs) lint
```

The expected output of the Lua conformance test is made with the reference implementation, Lua 5.5.1.
Lua 5.5.1 is needed only to regenerate it.

```sh
conformance/lua/golden/regen.sh
```

## ADRs and adr-guard

Changes to peg-hs start from an ADR (Architecture Decision Record), which records a design decision.
ADRs live in `docs/adr/`.

### Writing an ADR

- Write an ADR before implementing. Features and specification changes without an ADR are not accepted
- Name the file `NNNN-kebab-case.md`, where `NNNN` is the next number after the existing ADRs and the rest is an English name that tells what it is about
- Write ADRs in Japanese. Set the status to 提案 (proposed)
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

### Review and adoption

- Do not commit a new ADR; it is reviewed first
- Once adopted, set its status to 採択 (adopted) and commit it
- When adopting an ADR that changes the notation, update `docs/syntax.md` in the same commit and add the ADR to the list of reflected ADRs at its top
- When an ADR changes the specification, update `docs/specifications.md` and the README (both the English and the Japanese version) at the same time. These three must always be up to date on main
- When the way of development changes, update this document (both the Japanese and the English version) at the same time

### Committed ADRs do not change

- A committed ADR cannot be changed, except for its status line and the links of its references to ADRs. adr-guard checks this in the pre-commit hook and in the `adr` job of CI
- An ADR has exactly one status line, a line starting with `ステータス:`. adr-guard rejects an ADR with no status line or with two or more ([ADR 0043](docs/adr/0043-adr-guard-v0.8.0.md))
- To change a decision, write a new ADR with the change. Rewrite the status line of the original ADR as 採択→(the changed part)は ADR NNNN
- To discard an ADR, set its status to 破棄 (discarded) and write the reason in `docs/specifications.md`
- When an implementation could not follow its ADR, or took a different form, write an ADR that records it (for example [ADR 0015](docs/adr/0015-implementation-deviations.md), [ADR 0025](docs/adr/0025-lua-toml-implementation-deviations.md), [ADR 0029](docs/adr/0029-label-safety-implementation-deviations.md))

### Links to ADRs

A reference to an ADR (`ADR 0001`) in a document (`.md`) links to the file of the ADR.
adr-guard checks that the links are there.
After writing an ADR and after updating documents, run the following at the root of the repository to turn references without a link into links.

```sh
adr-guard links --fix
adr-guard links
```

When `adr-guard links` exits with 0, every reference has its link.

### Records that do not change

Benchmark records (`docs/benchmarks/`), conformance snapshots (`docs/conformance/`) and the records of the hand checks of the language server (`docs/editors/`) do not change after they are committed.
New results are added as new files.
Of these, adr-guard rejects changes only to `docs/benchmarks/`, adding links included ([ADR 0043](docs/adr/0043-adr-guard-v0.8.0.md)).
It does not check `docs/conformance/` and `docs/editors/`, so reviews check them.

## Rules of implementation

### Tests first

- Write the tests of the ADR's test design first, see them fail, then implement
- For a change that cannot be tested automatically (a setting, for example), write how to check it in the ADR's test design, and check it by running it after implementing
- Do not write tests without a bound on their running time. Write complexity checks with inputs small enough that a regression fails within seconds; an input that takes exponential time must show up as a failure, not as a test that never ends

### Compatibility of peg-runtime and the PVP

The versions of the packages follow the PVP.
Generated modules import `Peg.Runtime.Internal`, an internal module of peg-runtime.
Users do not use `Peg.Runtime.Internal` directly, but a change to it can break modules that were already generated, so it is a major change under the PVP ([ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md)).

The header comment of a generated module names the range of peg-runtime versions that the module needs (in the form `peg-runtime >=0.1 && <0.2`).
The range is the constant `runtimeVersions` of `Peg.Codegen` in peg-codegen.
When a change to `Peg.Runtime.Internal` breaks compatibility with generated modules, raise the range and regenerate the generated files with `scripts/regen-fixtures.sh`.
The tests of peg-codegen check that the range matches the range of the dependency on peg-runtime in `peg-codegen.cabal`.

### Dependencies

- If something can be reimplemented easily and its license allows it, reimplement it instead of adding a dependency. When only part of it is needed, implementing that part is enough
- Give reimplemented code thorough tests, modelled on the tests of the original

### Data of the conformance tests

Do not modify test data taken from elsewhere (`conformance/data/`).
Record the version and the source in `SOURCE`, and the license in `LICENSE`.

### Languages of the documents

- ADRs, the specification (`docs/specifications.md`) and the notation guide (`docs/syntax.md`) are written in Japanese
- Haddock of public modules is written in English
- The `CHANGELOG.md` of each package and the release notes are written in English
- Update both the English and the Japanese version of the README and of this document, with the same content

## Writing commits

- Split commits by what they are about. An ADR, its implementation, tests and document updates are often separate commits
- Write the subject and the body of a commit in English ([ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md))
- Write the subject in the form `type(scope): description`. The type is `feat`, `fix`, `test`, `docs`, `refactor`, `ci` and so on, and the scope is where the change is (a package name, or a place such as `editors`, `conformance`, `adr` or `benchmarks`); it may be left out when the change spans several places
- End the subject with the related ADR numbers in the form `(ADR 0046)`

```
feat(cli): take --name=value in every option that takes a value (ADR 0046)
```

- Do not rebase main. The only exception is a secret, such as an API key, committed by mistake
- Branches may be rebased until they are merged. Always merge with `--no-ff`

## CI jobs

CI consists of three workflows.

`.github/workflows/ci.yml` runs on pushes to main and on pull requests.
It does not run for changes of `docs/` and Markdown files only ([ADR 0039](docs/adr/0039-faster-ci.md)).
A new push to a pull request stops the run of the previous push.

- **haskell**: builds every package, and checks the grammars of the repository with `peg-hs fmt --check` and `peg-hs lint`, that the five packages have one version (`python3 scripts/versions.py check`), and each package with `cabal check`
- **test-grammar-1, test-grammar-2, test-grammar-3**: run peg-grammar-test in parts, `--shard 1/3` to `--shard 3/3` ([ADR 0042](docs/adr/0042-shard-peg-grammar-test.md))
- **test-conformance**: runs the conformance tests (Lua, TOML, JSON and CommonMark) and the complexity tests
- **test-packages**: runs the tests of peg-cli, peg-lsp, peg-codegen and peg-runtime
- **haddock**: generates the Haddock of the four published libraries, and checks with `scripts/haddock-coverage.sh` that every exposed module is fully documented ([ADR 0044](docs/adr/0044-release-v0-1-0.md))
- **sdist-1** to **sdist-3**: each makes the sdists of the five published packages, and builds and tests them from the unpacked tarballs alone. Each runs a third of peg-grammar-test with `--shard i/3`, and `sdist-2` also runs the other four suites. Each prints the number of skipped tests and their reasons ([ADR 0046](docs/adr/0046-docs-cli-and-ci-before-v0-1-0.md), [ADR 0051](docs/adr/0051-shard-tests-from-source-tarballs.md))
- **ghc-9.12.4, ghc-9.14.1**: build every package with the newer GHCs, and run the tests of peg-runtime and peg-codegen. The tests of peg-codegen check that generated modules compile without warnings ([ADR 0045](docs/adr/0045-fixes-before-v0-1-0.md))
- **editors**: runs the tests of the editor grammars, and checks that the committed tree-sitter parser is up to date ([ADR 0034](docs/adr/0034-syntax-highlighting.md))

In a test job (`test-*`), the suites run one at a time.
This gives each suite all the cores of the runner ([ADR 0041](docs/adr/0041-split-test-jobs-and-cores.md)).
A new test suite goes to the job that keeps the jobs about the same length, from the latest CI timings in `docs/benchmarks/`.

The **adr** job of `.github/workflows/adr.yml` runs on every change, documents included, and checks the ADRs and the benchmark records with adr-guard ([ADR 0047](docs/adr/0047-adr-guard-v0.8.1.md)).

`.github/workflows/release.yml` runs on a push of a tag starting with `v`, and makes a Release.
What it does is in "Release procedure".

## Benchmarks and performance

peg-hs sets no absolute performance targets ([ADR 0007](docs/adr/0007-performance-discipline.md)).
Measurements depend on the machine.
Regressions are found by measuring before and after a change on the same machine, and comparing.
CI does not check performance, because measurements on shared runners vary too much.

For changes touching peg-runtime or peg-codegen, run the following benchmarks before and after the change and compare them.

```sh
cabal bench peg-conformance
```

Before turning memoisation off for a rule with `%nomemo`, check where memo entries accumulate, and compare peak memory in separate processes ([ADR 0017](docs/adr/0017-nomemo-implementation.md)).

```sh
cd conformance && $(cabal list-bin peg-conformance:bench:peg-bench) --memo-report
```

Measurements behind performance decisions, and measurements of CI timings, go to `docs/benchmarks/` as dated snapshots.
They do not change after that (see "Records that do not change").

## Tests of the editor grammars

`editors/` holds a TextMate grammar, a tree-sitter grammar and a VS Code extension ([ADR 0034](docs/adr/0034-syntax-highlighting.md)).
Their tests run with Node and the tree-sitter CLI (installed by `npm ci`).

```sh
cd editors && npm ci && npm test
```

The tests check that the editor grammars find the same ranges (comments, literals, character classes, actions, rule names and labels) as the notation's own grammar.
The ranges they compare with are a golden file, `editors/test/ranges.txt`, which the tests of peg-grammar write.
After changing the notation, fix the grammars in `editors/`, rewrite `ranges.txt` with the following, and then run the tests of the editor grammars.

```sh
cabal test peg-grammar --test-options=--accept
```

The scopes of each token of the TextMate grammar are compared with `editors/test/textmate.golden.txt`.
When a change of scopes is intended, rewrite it with `UPDATE=1 npm test`.

After changing the tree-sitter grammar, also commit `editors/tree-sitter-hpeg/src`, which `npm test` regenerates.
The `editors` job of CI checks that regenerating it leaves no difference from the committed files.

## Release procedure

The scope and the procedure of releases are decided in [ADR 0044](docs/adr/0044-release-v0-1-0.md).

### Versions and tags

- The published packages are peg-runtime, peg-grammar, peg-codegen, peg-lsp and peg-cli, and all five are released with the same version
- A tag is `v` followed by the first three components of the cabal version (`v0.1.0`). The fourth component of the cabal version is for re-releases without a tag
- A pre-release tag has a mark after `-`, as in `v0.1.0-rc1`. Its cabal version is the three components before `-` (`0.1.0.0`), because PVP versions cannot express rc
- Tags starting with `v` are releases, and tags containing `-` are pre-releases

### 1. Raise the versions

Change the `version` of the five `.cabal` files and the ranges of the dependencies between the packages (`peg-runtime >=0.1 && <0.2` and so on) in one commit.
Then check that the versions agree:

```sh
python3 scripts/versions.py check
```

If compatibility of `Peg.Runtime.Internal` has broken, also raise `runtimeVersions` and regenerate the generated files (see "Compatibility of peg-runtime and the PVP").

### 2. Write the CHANGELOGs

Add a heading of the version (in the form `## 0.1.0.0`) to the `CHANGELOG.md` of each package.
Under it, group the changes under Added, Changed, Removed and Fixed, in English.
Give each change an absolute link to the ADR that decided it (`https://github.com/tett23/peg-hs/blob/main/docs/adr/...`).
Pre-releases do not get headings.
The changes of `v0.1.0-rc1` go under `## 0.1.0.0`, and fixes during the rc are added under the same heading.

### 3. Tag

Merge the version change and the CHANGELOGs to main, and check that CI on main passes.
Check locally that the version of the tag matches the versions of the `.cabal` files, then tag the commit of main and push the tag.

```sh
python3 scripts/versions.py tag v0.1.0-rc1
git tag v0.1.0-rc1
git push origin v0.1.0-rc1
```

### 4. Check the release workflow

Pushing the tag runs `.github/workflows/release.yml`, which does the following.

- Checks that the version of the tag matches the versions of the five `.cabal` files. If not, it fails and makes no Release
- Makes the sdists and the Haddock tarballs of the five packages, in the form that Hackage takes. The Haddock of peg-cli, which has executables only, is made with `--haddock-executables` ([ADR 0048](docs/adr/0048-release-commands-and-haddock-of-peg-cli.md))
- Builds the `peg-hs` executable for Linux (x86-64) and macOS (arm64)
- Creates a GitHub Release with the tarballs, the executables and `SHA256SUMS` attached, and publishes it. A tag containing `-` is published as a pre-release
- Puts GitHub's generated release notes (the pull requests merged since the previous tag) in the body as a placeholder

Running the workflow again for the same tag replaces the files of the existing Release.
Follow the run and check the attachments with:

```sh
gh run list --workflow release.yml
gh run watch
gh release view v0.1.0-rc1
```

### 5. Write the release notes

The release notes are written with Claude Code locally, after the Release exists.
They are not written in CI, so that no API credentials are stored in CI.
Give Claude Code the following instructions, with `TAG` (this tag) and `PREV` (the previous tag) replaced.
For a pre-release, `PREV` is the tag just before it (rc tags included); for a final version, it is the previous final version.

```
Write the release notes of peg-hs TAG and save them to release-notes.md
(outside the repository, or delete it afterwards; do not commit it).

Sources:
- the commits in `git log PREV..TAG`
- the pull requests merged in that range (`git log --merges PREV..TAG`,
  `gh pr list --state merged --base main`)
- the ADRs adopted in that range: `git diff --name-status PREV..TAG -- docs/adr/`,
  and the status lines that changed to 採択
- the CHANGELOG.md of each of the five packages (packages/*/CHANGELOG.md)

Format:
- English.
- Sections "Added", "Changed", "Removed" and "Fixed"; add other sections
  (for example "Documentation" or "CI") only when needed, and omit empty ones.
- Each item: one sentence on what changed for a user, then a link to its
  commit or pull request, and an absolute link to its ADR,
  https://github.com/tett23/peg-hs/blob/main/docs/adr/NNNN-name.md.
  Check that every ADR link points to an existing file.
- A section "Known limitations" with one line that links to
  https://github.com/tett23/peg-hs/blob/main/README.md#known-limitations
- A section "Assets" that names the attached files: the sdists and Haddock
  tarballs of the packages, the peg-hs executables for x86_64-linux and
  aarch64-macos, and SHA256SUMS.

If there is no previous tag (the first release), do not list changes; write
the features of each package, each with absolute links to the ADRs that
decided it, following the CHANGELOGs.
```

A person reads the notes, fixes any mistakes, and then replaces the body of the Release:

```sh
gh release edit v0.1.0-rc1 --notes-file release-notes.md
```

The person checks the grouping of the changes, the commit or pull request link of each item, that the absolute ADR links open, and the link to the known limitations.

### 6. Upload to Hackage

The workflow does not upload to Hackage, so that no Hackage credentials are stored in CI.
Download the attachments of the Release, check the checksums, and upload by hand with `cabal upload`.

```sh
gh release download v0.1.0-rc1 --dir release
cd release
shasum -a 256 -c SHA256SUMS
```

Without `--publish`, `cabal upload` uploads a candidate.
A candidate is for checking how the package looks on Hackage, and is kept apart from published versions.
Upload the packages in the order of their dependencies (peg-runtime, peg-grammar, peg-codegen, peg-lsp, peg-cli).

```sh
cabal upload peg-runtime-0.1.0.0.tar.gz peg-grammar-0.1.0.0.tar.gz peg-codegen-0.1.0.0.tar.gz peg-lsp-0.1.0.0.tar.gz peg-cli-0.1.0.0.tar.gz
cabal upload --documentation peg-runtime-0.1.0.0-docs.tar.gz peg-grammar-0.1.0.0-docs.tar.gz peg-codegen-0.1.0.0-docs.tar.gz peg-lsp-0.1.0.0-docs.tar.gz peg-cli-0.1.0.0-docs.tar.gz
```

On the candidate pages, check the documentation of the modules, the description and examples at the top of each module, the CHANGELOG and the dependencies.

- **Pre-releases (`v0.1.0-rc1` and so on)**: upload as candidates and check them only; never publish. Hackage versions cannot express rc, and once `0.1.0.0` is published it cannot be taken back
- **Final versions (`v0.1.0` and so on)**: after uploading and checking the candidates, upload the same files with `--publish` to publish them

```sh
cabal upload --publish peg-runtime-0.1.0.0.tar.gz peg-grammar-0.1.0.0.tar.gz peg-codegen-0.1.0.0.tar.gz peg-lsp-0.1.0.0.tar.gz peg-cli-0.1.0.0.tar.gz
cabal upload --publish --documentation peg-runtime-0.1.0.0-docs.tar.gz peg-grammar-0.1.0.0-docs.tar.gz peg-codegen-0.1.0.0-docs.tar.gz peg-lsp-0.1.0.0-docs.tar.gz peg-cli-0.1.0.0-docs.tar.gz
```

After publishing a final version, update the status at the top of the README and of this document to say that peg-hs is on Hackage.

### Hand checks of the language server

The language server is checked by hand in VS Code, Neovim and Helix: diagnostics, formatting, go to definition, hover, document symbols and semantic tokens.
The owner of the repository does this when convenient.
It is not a condition of a release, rc or otherwise.
The results (the editor and its version, the features checked, the problems) go to `docs/editors/` as records, which do not change after they are committed.
The commit that adds a record removes the "unverified" note from the README's configuration example for that editor.

## License

peg-hs is licensed under the MIT License.
Contributions are published under the MIT License.
