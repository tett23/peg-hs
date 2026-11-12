#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
for grammar in packages/peg-grammar/grammar/Peg.hpeg packages/peg-grammar/grammar/PegSyntax.hpeg; do
  actual=$({
    sed -n -e '/^paramFormMessage ::/,/^param l c =/p' -e '/^ParamChunk <-/p' -e '/^TypeText <-/p' -e '/^ArgChunk <-/p' "$grammar"
    sed -n -e '/^isIdentStart ::/,/^  Nothing -> False$/p' -e '/^toParam ::/,/^  _ -> Left /p' \
      packages/peg-grammar/src/Peg/Grammar/Assemble.hs
  } | shasum -a 256 | cut -d ' ' -f 1)
  [ "$actual"  = 1cd290539739bbfb454b333ad608887290425eecc2936bd0723b3cac9769b23b ] || { echo "review parameter predicates for $grammar" >&2; exit 1; }
done
