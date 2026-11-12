#!/bin/sh
# The two metagrammars use the same depth actions. Include the entire relevant
# productions so moving a guard or changing a child argument invalidates it.
set -eu
cd "$(dirname "$0")/.."
project_depth() {
  sed -n -e '/^maxDepth ::/,/^applyOp ::/{ /^--/!p; }' \
    -e '/^Alt <- /p' \
    -e '/^Item(d :: Int) ::/,/^MoreGroup <- /{ /^#/!p; }' "$1" | sed '/^$/d'
}
for grammar in packages/peg-grammar/grammar/Peg.hpeg packages/peg-grammar/grammar/PegSyntax.hpeg; do
  actual=$(project_depth "$grammar" | shasum -a 256 | cut -d ' ' -f 1)
  [ "$actual" = bc8c82a6cc96cca02a5fd495e5d2fdfd7f8f45cc6bd46f4105032de6c097ac3f ] || { echo "review depth proof for $grammar" >&2; exit 1; }
done
