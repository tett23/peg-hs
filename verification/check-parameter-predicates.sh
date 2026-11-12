#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
for grammar in packages/peg-grammar/grammar/Peg.hpeg packages/peg-grammar/grammar/PegSyntax.hpeg; do
  actual=$({
    sed -n -e '/^paramFormMessage ::/,/^param l c =/p' -e '/^ParamChunk <-/p' "$grammar"
    sed -n -e '/^isIdentStart ::/,/^  Nothing -> False$/p' -e '/^toParam ::/,/^  _ -> Left /p' \
      packages/peg-grammar/src/Peg/Grammar/Assemble.hs
  } | shasum -a 256 | cut -d ' ' -f 1)
  [ "$actual" = bc816993df6a874ca151da4f7382035eb747f9db5c515723b2627eebed10137f ] || { echo "review parameter predicates for $grammar" >&2; exit 1; }
done
