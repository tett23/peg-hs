#!/bin/sh
# ADR 0097: Peg.Grammar.Assemble is translated into Lean from GHC's syntax
# tree by TranslateHaskell.hs (no fixed copy of the source), and the proofs
# AssembleTextProof, AssembleExportProof, AssembleStringProof,
# AssembleDirectiveProof and AssembleTranslatedProof show the translation
# equal to the models AssemblePredicates, AssembleValidationHelpers,
# DirectiveNames, BoundedDecimal and AssembleValidation on every input. Pass
# the directory of the compiled Lean modules (check.sh's work directory, with
# HsPrelude and AssembleValidation compiled); the script writes
# AssembleTranslated and the proofs there.
#
# Mutants: two changes of Assemble.hs outside the translator's subset (a tuple
# section, a library function outside the table) stop the translation; a
# change that drops a case of nestedExpr translates and compiles, and the
# proof rejects it.
set -eu

cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of the compiled Lean modules}
ghc=${GHC:-ghc-9.10.3}
[ "$($ghc --numeric-version)" = 9.10.3 ] || {
  echo 'GHC 9.10.3 is required' >&2
  exit 1
}
libdir=$("$ghc" --print-libdir)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# 1. The translator, with GHC's own front end.
mkdir -p "$work/build"
# The record updates of GHC's syntax tree miss its extension constructors.
"$ghc" -package ghc -O0 -Wall -Werror -Wno-incomplete-record-updates -outputdir "$work/build" \
  verification/TranslateHaskell.hs -o "$work/translate" > "$work/build.log" 2>&1 || {
  cat "$work/build.log" >&2
  exit 1
}
roots="assemble toParam isValidIdent isIdentStart isIdentChar advanceLoc verbatimBody directiveArg directiveComment isImportPath isModuleName"
translate() {
  # shellcheck disable=SC2086
  "$work/translate" "$libdir" "$1/peg-grammar/src" "$1/peg-grammar/src/Peg/Grammar/Assemble.hs" \
    AssembleTranslated verification/translate-assemble.hints $roots
}

# 2. Data.Char.generalCategory of GeneralCategory.lean is GHC's (rule H10).
runghc-9.10.3 -Wall -Werror verification/ExtractGeneralCategory.hs > "$work/categories"
sed -n '/^def generalCategoryRanges : List (Nat × Nat × Nat) := \[$/,/^]$/p' verification/GeneralCategory.lean |
  sed '1d;$d' > "$work/categories-committed"
diff -u "$work/categories" "$work/categories-committed"

# 3. Translate the module, compile the translation and the proofs.
proofs="AssembleTextProof AssembleExportProof AssembleStringProof AssembleDirectiveProof AssembleTranslatedProof"
mkdir -p "$work/src"
cp -R packages/peg-grammar "$work/src/peg-grammar"
translate "$work/src" > "$lean_objects/AssembleTranslated.lean"
(cd verification &&
  LEAN_PATH="$lean_objects" lean -DwarningAsError=true -R "$lean_objects" \
    -o "$lean_objects/AssembleTranslated.olean" "$lean_objects/AssembleTranslated.lean" &&
  for module in $proofs; do
    LEAN_PATH="$lean_objects" lean -DwarningAsError=true -o "$lean_objects/$module.olean" "$module.lean"
  done)

# 4. Mutants.
mutant() {
  rm -rf "$work/mutant"
  mkdir -p "$work/mutant"
  cp -R packages/peg-grammar "$work/mutant/peg-grammar"
  sed "$1" packages/peg-grammar/src/Peg/Grammar/Assemble.hs > "$work/mutant/peg-grammar/src/Peg/Grammar/Assemble.hs"
  if cmp -s packages/peg-grammar/src/Peg/Grammar/Assemble.hs "$work/mutant/peg-grammar/src/Peg/Grammar/Assemble.hs"; then
    echo "the mutant $2 changes nothing" >&2
    exit 1
  fi
}
rejected=0
mutant 's/^    imports = \[(l, al, a) | TDirective l "import" al a <- items\]$/    imports = [fst ((, ()) (l, al, a)) | TDirective l "import" al a <- items]/' tuple-section
if translate "$work/mutant" > "$work/mutant.lean" 2> "$work/mutant.err"; then
  echo 'the translator took a tuple section' >&2
  exit 1
fi
grep -q 'unsupported: a tuple section' "$work/mutant.err"
rejected=$((rejected + 1))
mutant 's/^    defs = \[(l, n, alts) | TDef l n _ alts <- items\]$/    defs = init [(l, n, alts) | TDef l n _ alts <- items]/' library
if translate "$work/mutant" > "$work/mutant.lean" 2> "$work/mutant.err"; then
  echo 'the translator took a library function outside its table' >&2
  exit 1
fi
grep -q 'unsupported: the name GHC.List.init' "$work/mutant.err"
rejected=$((rejected + 1))
# The case is replaced by a comment, so that the lines after it keep their
# numbers (the names of the lifted functions carry them).
mutant 's/^      EStar e -> nestedExpr e$/      -- EStar e -> nestedExpr e/' nested-star
translate "$work/mutant" > "$work/mutant/AssembleTranslated.lean"
mkdir -p "$work/mutant/olean"
(cd verification &&
  LEAN_PATH="$work/mutant/olean:$lean_objects" lean -DwarningAsError=true -R "$work/mutant" \
    -o "$work/mutant/olean/AssembleTranslated.olean" "$work/mutant/AssembleTranslated.lean" &&
  for module in AssembleTextProof AssembleExportProof AssembleStringProof AssembleDirectiveProof; do
    LEAN_PATH="$work/mutant/olean:$lean_objects" lean -DwarningAsError=true \
      -o "$work/mutant/olean/$module.olean" "$module.lean"
  done)
if (cd verification && LEAN_PATH="$work/mutant/olean:$lean_objects" lean -DwarningAsError=true \
  AssembleTranslatedProof.lean > "$work/mutant-proof.log" 2>&1); then
  echo 'the proof took nestedExpr without its case for EStar' >&2
  exit 1
fi
grep -q 'nestedExpr' "$work/mutant-proof.log" || {
  cat "$work/mutant-proof.log" >&2
  exit 1
}
rejected=$((rejected + 1))
printf 'Assemble.hs translated from the GHC syntax tree; %s mutants rejected.\n' "$rejected"
