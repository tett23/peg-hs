#!/bin/sh
# Builds the wasm reactor of ADR 0078 and writes it to OUT (ADR 0079):
# builds exe:peg-hs-wasm with cabal.project.wasm, merges wasm/stubs.wat into
# it as the module wasi_snapshot_preview1, so that the imports outside the
# import contract become functions of the wasm, and removes the exports
# other than those of wasm/exports.json. The tools of ghc-wasm-meta
# (wasm32-wasi-cabal, wasm-tools, wasm-merge, wasm-metadce) must be on PATH:
#
#   nix shell "gitlab:haskell-wasm/ghc-wasm-meta/8079eb96bbc63823d99ad8acaff0765532625474?host=gitlab.haskell.org#all_9_10" \
#     -c scripts/build-wasm.sh peg-hs.wasm
#
# RAW, if given, is where the wasm before the merge is copied, for the
# test of wasm/stubs.wat.
#
#   scripts/build-wasm.sh OUT [RAW]
set -eu

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
  echo "usage: $0 OUT [RAW]" >&2
  exit 2
fi
case $1 in
  /*) out=$1 ;;
  *) out=$(pwd)/$1 ;;
esac
raw_copy=
if [ $# -eq 2 ]; then
  case $2 in
    /*) raw_copy=$2 ;;
    *) raw_copy=$(pwd)/$2 ;;
  esac
fi
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
trap 'exit 1' INT TERM

wasm32-wasi-cabal build --project-file=cabal.project.wasm exe:peg-hs-wasm
raw=$(wasm32-wasi-cabal list-bin --project-file=cabal.project.wasm exe:peg-hs-wasm)
# list-bin names the file without the extension that the linker gives it.
if [ ! -f "$raw" ] && [ -f "$raw.wasm" ]; then
  raw=$raw.wasm
fi
if [ -n "$raw_copy" ]; then
  cp "$raw" "$raw_copy"
fi

wasm-tools parse wasm/stubs.wat -o "$work/stubs.wasm"
wasm-merge "$raw" main "$work/stubs.wasm" wasi_snapshot_preview1 -o "$work/merged.wasm"
wasm-metadce "$work/merged.wasm" --graph-file wasm/exports.json -o "$work/final.wasm"
cp "$work/final.wasm" "$out"
echo "wrote $1 ($(wc -c < "$out" | tr -d ' ') bytes)"
