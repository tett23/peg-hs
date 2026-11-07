# Changelog of peg-hooks

The format follows the release notes of peg-hs: each version lists what was
Added, Changed, Removed and Fixed, with the ADRs that decided it.

## 0.1.0.0

The first release. peg-hooks generates the modules of the grammars of a
cabal package in its build.

### Added

Since v0.1.0-rc5:

- `Peg.Hooks.pegSetupHooks`, the setup hooks of a package with
  `build-type: Hooks`: before each component is built, a rule generates
  the module of each `Grammar` of the package into the autogen directory,
  with the checks and the warnings of `peg-hs gen`. A `%module` other than
  the module name of the `Grammar` stops the build
  ([ADR 0085](https://github.com/tett23/peg-hs/blob/main/docs/adr/0085-generate-modules-in-the-build-with-setup-hooks.md)).
