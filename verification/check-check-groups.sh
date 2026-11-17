#!/bin/sh
# Ties CheckGroupsModel.lean to Peg.Grammar.Check: the whole Haskell module
# and the spans of the other modules that the model translates are fixed,
# and the model gives the same result of check and checkLibrary, and the
# same errors of each group that is a function of the module, as the real
# functions on the grammars of CheckGroupsProbe.hs. Pass the directory that
# holds the compiled Lean modules (check.sh's work directory).
set -eu

cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of the compiled Lean modules}
source_file=packages/peg-grammar/src/Peg/Grammar/Check.hs
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# 1. The source that CheckGroupsModel translates. A change to it requires
# reviewing the translation and updating check-groups.source.
diff -u verification/check-groups.source "$source_file"

# 2. The functions of other modules that the model translates: hasValue,
# countedItems and isUnit, isClassified and valueRefs of Peg.Grammar.Types,
# and syntaxTypeName of Peg.Grammar (its isUpper and toUpper are tables of
# the probe).
types=packages/peg-grammar/src/Peg/Grammar/Types.hs
sed -n '/^hasValue ::/,/^fieldItems ::/p' "$types" > "$work/values"
[ "$(git hash-object "$work/values")" = 9c8eb0f4dd7e534d54c1b3042d75f3eab964eba7 ]
sed -n '/^isClassified ::/,/^    && all (isNothing . altAction) (ruleAlts r)$/p' "$types" > "$work/classified"
[ "$(git hash-object "$work/classified")" = 057597d9199a364bb45191d3066e5d1c640c5353 ]
sed -n '/^valueRefs ::/,/^  _ -> \[\]$/p' "$types" > "$work/valuerefs"
[ "$(git hash-object "$work/valuerefs")" = 0ddfc8955b0f99ec7c8a279c303c1ff317a30cbb ]
sed -n '/^syntaxTypeName ::/,/^  _ -> "Rule.*Syntax"$/p' packages/peg-grammar/src/Peg/Grammar.hs > "$work/syntax-name"
[ "$(git hash-object "$work/syntax-name")" = c868734c53e6f508d745e730b54b3a25dcb744a6 ]

# 3. The rejection of the generation (CheckGroupsTheorems.generation_rejects):
# generate and generateWithWarnings return the errors of check, through
# templateNotes, which maps each and removes the duplicates.
sed -n '/^templateNotes ::/,/^templateNotes g = nub . map note$/p' \
  packages/peg-grammar/src/Peg/Grammar/Templates.hs > "$work/notes"
[ "$(git hash-object "$work/notes")" = 99602d2df0a58f737c6e8dae69869ca4b032d066 ]
codegen=packages/peg-codegen/src/Peg/Codegen.hs
[ "$(grep -c '^  analysis <- either (Left . templateNotes g0) Right (check g)$' "$codegen")" = 1 ]
[ "$(grep -c '^  g <- either (Left . templateNotes g0) Right (expandTemplates g0 >>= \\g -> g <\$ check g)$' "$codegen")" = 1 ]

# 4. The probe: the real functions, and the module under another name for
# the functions it does not export.
sed -e 's/^module Peg.Grammar.Check$/module CheckInternal where/' -e '/^  ( Analysis (..)$/,/^  ) where$/d' \
  "$source_file" > "$work/CheckInternal.hs"
run_probe() {
  "${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-grammar -package=directory -package=filepath \
    --ghc-arg=-i"$work" --ghc-arg=-Wall --ghc-arg=-Werror verification/CheckGroupsProbe.hs "$1"
}
run_probe lean > "$work/CheckGroupsProbeCases.lean"
run_probe expect > "$work/haskell-output"

(cd verification &&
  LEAN_PATH="$work:$lean_objects" lean -DwarningAsError=true -R "$work" \
    -o "$work/CheckGroupsProbeCases.olean" "$work/CheckGroupsProbeCases.lean" &&
  LEAN_PATH="$work:$lean_objects" lean -DwarningAsError=true \
    --run CheckGroupsProbe.lean > "$work/lean-output")

diff -u "$work/haskell-output" "$work/lean-output"
printf 'Check groups: %s grammars, %s rejected, %s errors agree.\n' \
  "$(grep -c '^case ' "$work/lean-output")" \
  "$(awk '/^case /{if (e) n++; e=0} /^error /{e=1} END{if (e) n++; print n+0}' "$work/lean-output")" \
  "$(grep -c '^error ' "$work/lean-output")"
