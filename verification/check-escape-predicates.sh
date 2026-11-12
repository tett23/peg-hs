#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
for grammar in packages/peg-grammar/grammar/Peg.hpeg packages/peg-grammar/grammar/PegSyntax.hpeg; do
  # Include character decoding and the exact capture each predicate reads.
  actual=$(sed -n -e '/^tokens ::/,/^nonEmptyRanges item =/p' \
    -e '/^Escape <-/,/^ClassChar <-/p' "$grammar" | shasum -a 256 | cut -d ' ' -f 1)
  [ "$actual" = 9252c155e981844b8e3dd7c34f504b54ddb314e8bcb5ace733574b1da50b0835 ] || { echo "review escape predicates for $grammar" >&2; exit 1; }
done
