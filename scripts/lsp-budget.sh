#!/bin/sh
# The measuring command of the language-server budgets of docs/budgets.md
# (ADR 0102). Measures the working tree with scripts/lsp-measure.sh and the
# Memo grammar of conformance/bench, and prints the largest median of the six
# cases of OPERATION in ms, with three decimals, as the last line of the
# standard output. The value run on a developer's machine is for reference:
# the judgment of pull requests and the measurement of main decide the
# budgets.
#
#   scripts/lsp-budget.sh diagnostics|semantic-tokens
set -eu

if [ $# -ne 1 ]; then
  echo "usage: $0 diagnostics|semantic-tokens" >&2
  exit 2
fi
case $1 in
  diagnostics|semantic-tokens) ;;
  *)
    echo "usage: $0 diagnostics|semantic-tokens" >&2
    exit 2
    ;;
esac

root=$(cd "$(dirname "$0")/.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "$root"
scripts/lsp-measure.sh conformance/bench/Memo.hpeg "$out"
node scripts/lsp-median.mjs --max "$1" "$out/Memo.json" "$out/Golem.json"
