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
  "$peg" gen grammar/Peg.peg -o src/Peg/Grammar/SelfHosted.hs >/dev/null
  # The variant with a lossless syntax tree and recovery, for the formatter
  # and the language server (ADR 0032, ADR 0035).
  sed -e 's/^%module Peg.Grammar.SelfHosted$/%module Peg.Grammar.SelfHostedSyntax/' \
    -e 's/^TopItem <- t:TopOne Ws { t }$/TopItem <- \&. t:(TopOne ^topitem) Ws { t }/' grammar/Peg.peg > grammar/PegSyntax.peg
  cat grammar/SyntaxVariant.txt >> grammar/PegSyntax.peg
  "$peg" gen grammar/PegSyntax.peg -o src/Peg/Grammar/SelfHostedSyntax.hs >/dev/null
)
# Rebuild, since the generator itself contains the parser just generated.
"$cabal" build exe:peg-hs >/dev/null

# Codegen fixtures: generated with the debug entry, paths relative to the package.
(
  cd packages/peg-codegen
  for src in test/fixtures/*.peg; do
    name=$(basename "$src" .peg)
    "$peg" gen "$src" -o "test/generated/Fixture/$name.hs" --debug-entry >/dev/null
  done
  # Golden output of the default options.
  "$peg" gen test/fixtures/Sum.peg -o test/golden/Sum.hs.golden >/dev/null
  # The recovery fixture without its labels, for the label safety tests (ADR 0028).
  "$peg" gen test/fixtures/Recover.peg -o test/generated/Fixture/RecoverNoLabels.hs --strip-labels Fixture.RecoverNoLabels >/dev/null
)
# The notation's grammar without its labels, for the label safety tests (ADR 0028).
(
  cd packages/peg-grammar
  "$peg" gen grammar/Peg.peg -o test/generated/SelfHostedNoLabels.hs --strip-labels SelfHostedNoLabels >/dev/null
)

# Conformance grammars.
if [ -d conformance/json ]; then
  (
    cd conformance
    "$peg" gen json/Json.peg -o json/Conformance/Json/Parser.hs >/dev/null
    # The JSON parser of the language server (ADR 0035), from the same grammar.
    sed 's/^%module Conformance.Json.Parser$/%module Peg.Lsp.JsonParser/' json/Json.peg > ../packages/peg-lsp/grammar/Json.peg
    (cd ../packages/peg-lsp && "$peg" gen grammar/Json.peg -o src/Peg/Lsp/JsonParser.hs >/dev/null)
    # Variants of the JSON grammar for ADR 0017, derived from json/Json.peg.
    sed 's/^%module Conformance.Json.Parser$/%module Conformance.Bench.JsonCounted/' json/Json.peg > bench/JsonCounted.peg
    sed 's/^%module Conformance.Json.Parser$/%module Conformance.Bench.JsonNomemo\n%nomemo Ws\n%nomemo Unit\n%nomemo Hex\n%nomemo IntPart\n%nomemo Frac\n%nomemo Exp/' json/Json.peg > bench/JsonNomemo.peg
    sed 's/^%module Conformance.Json.Parser$/%module Conformance.Bench.JsonSyntax\n%syntax\n%token Ws\n%trivia Ws/' json/Json.peg > bench/JsonSyntax.peg
    "$peg" gen bench/JsonSyntax.peg -o bench/Conformance/Bench/JsonSyntax.hs --debug-entry >/dev/null
    "$peg" gen bench/JsonCounted.peg -o bench/Conformance/Bench/JsonCounted.hs --debug-entry >/dev/null
    # Written by hand: the JSON grammar with labels and recovery rules (ADR 0021).
    "$peg" gen bench/JsonRecover.peg -o bench/Conformance/Bench/JsonRecover.hs >/dev/null
    "$peg" gen bench/JsonNomemo.peg -o bench/Conformance/Bench/JsonNomemo.hs --debug-entry >/dev/null
    "$peg" gen bench/Pathological.peg -o bench/Conformance/Bench/Pathological.hs --debug-entry >/dev/null
    for n in 2 4 8; do
      "$peg" gen bench/NestedLR$n.peg -o bench/Conformance/Bench/NestedLR$n.hs --debug-entry >/dev/null
    done
    "$peg" gen lua/Lua.peg -o lua/Conformance/Lua/Parser.hs --debug-entry >/dev/null
    "$peg" gen toml/Toml.peg -o toml/Conformance/Toml/Parser.hs >/dev/null
    "$peg" gen toml/Toml.peg -o toml/Conformance/Toml/NoLabels.hs --strip-labels Conformance.Toml.NoLabels >/dev/null
    "$peg" gen commonmark/Block.peg -o commonmark/Conformance/CommonMark/Block.hs >/dev/null
    "$peg" gen commonmark/Inline.peg -o commonmark/Conformance/CommonMark/Inline.hs >/dev/null
    "$peg" gen commonmark/v1/Block.peg -o commonmark/Conformance/CommonMark/V1/Block.hs >/dev/null
    "$peg" gen commonmark/v1/Inline.peg -o commonmark/Conformance/CommonMark/V1/Inline.hs >/dev/null
  )
fi

# The sources that peg-hs parse compiles (ADR 0036).
python3 scripts/embed-runtime.py

echo "regenerated"
