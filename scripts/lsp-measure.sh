#!/bin/sh
# Measures the edit latency of the language server (ADR 0102). Builds the
# peg-bench of the working tree in the current directory with -O1, fetches
# the Golem grammar of a fixed commit and checks its SHA-256, and measures
# the Memo grammar given and the Golem grammar with RTS -A64m. Writes
# Memo.json and Golem.json, the Criterion reports, to OUT. The measurement
# of main (lsp-latency.yml), the judgment of pull requests (ci.yml) and
# scripts/lsp-budget.sh all measure with this script.
#
#   scripts/lsp-measure.sh MEMO OUT
#
# CABAL selects the cabal to use (default: cabal).
set -eu

if [ $# -ne 2 ]; then
  echo "usage: $0 MEMO OUT" >&2
  exit 2
fi

golem=89ae4b4142c58cb8937e10c18c0e664280397547
golem_sha256=e27f6daf94af567afbf0712eae8f2ec4e9d45801571b61b90af04929020d1a2c
cabal=${CABAL:-cabal}

memo=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
mkdir -p "$2"
out=$(cd "$2" && pwd)

curl --fail --silent --show-error --location --retry 3 -o "$out/Golem.hpeg" \
  "https://raw.githubusercontent.com/tett23/golem/$golem/modules/golem-parser/grammar/Golem.hpeg"
if command -v sha256sum > /dev/null; then
  sum=$(sha256sum "$out/Golem.hpeg")
else
  sum=$(shasum -a 256 "$out/Golem.hpeg")
fi
if [ "${sum%% *}" != "$golem_sha256" ]; then
  echo "$0: the SHA-256 of Golem.hpeg does not match" >&2
  exit 1
fi
cp "$memo" "$out/Memo.hpeg"

"$cabal" build bench:peg-bench --enable-optimization=1
bench=$("$cabal" list-bin bench:peg-bench --enable-optimization=1)
cd conformance
for grammar in Memo Golem; do
  PEG_BENCH_LSP_GRAMMAR="$out/$grammar.hpeg" "$bench" \
    --match pattern range --json "$out/$grammar.json" +RTS -A64m -RTS
done
