#!/bin/sh
# Regenerate the committed generated modules from their grammars.
# The tests check that the committed files match the generator's output,
# so run this after changing the generator or a fixture grammar.
set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
cabal=${CABAL:-cabal}
"$cabal" build exe:peg-hs >/dev/null
peg=$("$cabal" list-bin exe:peg-hs)

# The self-hosted parser of the notation (the stage 11 of ADR 0013).
(
  cd packages/peg-grammar
  "$peg" grammar/Peg.peg -o src/Peg/Grammar/SelfHosted.hs >/dev/null
)
# Rebuild, since the generator itself contains the parser just generated.
"$cabal" build exe:peg-hs >/dev/null

# Codegen fixtures: generated with the debug entry, paths relative to the package.
(
  cd packages/peg-codegen
  for src in test/fixtures/*.peg; do
    name=$(basename "$src" .peg)
    "$peg" "$src" -o "test/generated/Fixture/$name.hs" --debug-entry >/dev/null
  done
  # Golden output of the default options.
  "$peg" test/fixtures/Sum.peg -o test/golden/Sum.hs.golden >/dev/null
)

# Conformance grammars.
if [ -d conformance/json ]; then
  (
    cd conformance
    "$peg" json/Json.peg -o json/Conformance/Json/Parser.hs >/dev/null
    "$peg" bench/Pathological.peg -o bench/Conformance/Bench/Pathological.hs --debug-entry >/dev/null
    "$peg" commonmark/Block.peg -o commonmark/Conformance/CommonMark/Block.hs >/dev/null
    "$peg" commonmark/Inline.peg -o commonmark/Conformance/CommonMark/Inline.hs >/dev/null
    "$peg" commonmark/v1/Block.peg -o commonmark/Conformance/CommonMark/V1/Block.hs >/dev/null
    "$peg" commonmark/v1/Inline.peg -o commonmark/Conformance/CommonMark/V1/Inline.hs >/dev/null
  )
fi

echo "regenerated"
