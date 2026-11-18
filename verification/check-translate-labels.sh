#!/bin/sh
# ADR 0097: Peg.Grammar.Labels is translated into Lean from GHC's syntax tree
# by TranslateHaskell.hs (no fixed copy of the source), and
# LabelsTranslatedProof.lean proves the translation equal to the model
# LabelCheckModel. Pass the directory of the compiled Lean modules (check.sh's
# work directory, with AssembleChars and LabelCheckModel compiled); the script
# writes HsPrelude, LabelsTranslated and LabelsTranslatedProof there.
#
# Mutants: two changes of Labels.hs outside the translator's subset (a tuple
# section, a library function outside the table) stop the translation; a
# change that drops a case of stripLabels translates and compiles, and the
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
roots="labelWarnings labelSafeAt matchesEmpty stripLabels stripLabelsAs"
translate() {
  # shellcheck disable=SC2086
  "$work/translate" "$libdir" "$1/peg-grammar/src" "$1/peg-grammar/src/Peg/Grammar/Labels.hs" \
    LabelsTranslated verification/translate-labels.hints $roots
}

# 2. Data.Char.isSpace of HsPrelude is GHC's.
cat > "$work/Space.hs" <<'SOURCE'
import Data.Char (chr, isSpace)
import Numeric (showHex)
main :: IO ()
main = mapM_ (\(a, b) -> putStrLn ("  (0x" ++ showHex a "" ++ ", 0x" ++ showHex b "" ++ "),")) (spans [p | p <- [0 .. 0xD7FF] ++ [0xE000 .. 0x10FFFF], isSpace (chr p)])
  where
    spans (p : ps) = go p p ps
    spans [] = []
    go a b (q : qs) | q == b + 1 = go a q qs
    go a b qs = (a, b) : spans qs
SOURCE
runghc-9.10.3 "$work/Space.hs" > "$work/space"
sed -n '/^def spaceRanges : List (Nat × Nat) := \[$/,/^]$/p' verification/HsPrelude.lean | sed '1d;$d' > "$work/space-committed"
diff -u "$work/space" "$work/space-committed"

# 3. Translate the module, compile the translation and the proof.
mkdir -p "$work/src"
cp -R packages/peg-grammar "$work/src/peg-grammar"
translate "$work/src" > "$lean_objects/LabelsTranslated.lean"
(cd verification &&
  LEAN_PATH="$lean_objects" lean -DwarningAsError=true -o "$lean_objects/HsPrelude.olean" HsPrelude.lean &&
  LEAN_PATH="$lean_objects" lean -DwarningAsError=true -R "$lean_objects" \
    -o "$lean_objects/LabelsTranslated.olean" "$lean_objects/LabelsTranslated.lean" &&
  LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
    -o "$lean_objects/LabelsTranslatedProof.olean" LabelsTranslatedProof.lean)

# 4. Mutants.
mutant() {
  rm -rf "$work/mutant"
  mkdir -p "$work/mutant"
  cp -R packages/peg-grammar "$work/mutant/peg-grammar"
  sed "$1" packages/peg-grammar/src/Peg/Grammar/Labels.hs > "$work/mutant/peg-grammar/src/Peg/Grammar/Labels.hs"
  if cmp -s packages/peg-grammar/src/Peg/Grammar/Labels.hs "$work/mutant/peg-grammar/src/Peg/Grammar/Labels.hs"; then
    echo "the mutant $2 changes nothing" >&2
    exit 1
  fi
}
rejected=0
mutant 's/      | otherwise = r : go (unLoc r : seen) rs/      | otherwise = fst ((, ()) r) : go (unLoc r : seen) rs/' tuple-section
if translate "$work/mutant" > "$work/mutant.lean" 2> "$work/mutant.err"; then
  echo 'the translator took a tuple section' >&2
  exit 1
fi
grep -q 'unsupported: a tuple section' "$work/mutant.err"
rejected=$((rejected + 1))
mutant 's/    recoveryEntries = go (start : map unLoc (grammarEntries g))/    recoveryEntries = go (start : reverse (map unLoc (grammarEntries g)))/' library
if translate "$work/mutant" > "$work/mutant.lean" 2> "$work/mutant.err"; then
  echo 'the translator took a library function outside its table' >&2
  exit 1
fi
grep -q 'unsupported: the name GHC.List.reverse' "$work/mutant.err"
rejected=$((rejected + 1))
mutant '/^      EStar x -> EStar (expr x)$/d' strip-star
translate "$work/mutant" > "$work/mutant/LabelsTranslated.lean"
mkdir -p "$work/mutant/olean"
(cd verification &&
  LEAN_PATH="$work/mutant/olean:$lean_objects" lean -DwarningAsError=true -R "$work/mutant" \
    -o "$work/mutant/olean/LabelsTranslated.olean" "$work/mutant/LabelsTranslated.lean")
if (cd verification && LEAN_PATH="$work/mutant/olean:$lean_objects" lean -DwarningAsError=true LabelsTranslatedProof.lean > "$work/mutant-proof.log" 2>&1); then
  echo 'the proof took stripLabels without its case for *' >&2
  exit 1
fi
rejected=$((rejected + 1))
printf 'Labels.hs translated from the GHC syntax tree; %s mutants rejected.\n' "$rejected"
