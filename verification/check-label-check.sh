#!/bin/sh
# Ties LabelCheckModel.lean to Peg.Grammar.Labels: the whole Haskell module
# is fixed, the isSpace table of the model is GHC's, and the model gives the
# same warnings, stripped grammars, left recursion and nullable rules as the
# real functions on the grammars of LabelCheckProbe.hs. Pass the directory
# that holds the compiled Lean modules (check.sh's work directory).
set -eu

cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of the compiled Lean modules}
source_file=packages/peg-grammar/src/Peg/Grammar/Labels.hs
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# 1. The source that LabelCheckModel translates. A change to it requires
# reviewing the translation and updating label-check.source.
diff -u verification/label-check.source "$source_file"

# 2. The rejection on labels of peg-hs gen: the warnings are those of
# labelWarnings, and --Werror fails exactly when there is one
# (LabelCheckTheorems.werror_rejects_iff).
sed -n '/^generateWithWarnings ::/,/^  pure (Generation target warnings (generate opts target))$/p' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$work/generation"
[ "$(git hash-object "$work/generation")" = 046184bee60a6b976cea7981c8fa02f1b4d04237 ]
sed -n '/^      let warnings = generationWarnings gen$/,/^        then pure (ExitFailure 1)$/p' \
  packages/peg-cli/app/Command/Gen.hs > "$work/werror"
[ "$(git hash-object "$work/werror")" = e83340023edcfe0943f3c93302168c8325bdfacd ]

# 3. Data.Char.isSpace on every Unicode scalar value.
[ "$(ghc-9.10.3 --numeric-version)" = 9.10.3 ] || {
  echo 'GHC 9.10.3 is required for the isSpace table.' >&2
  exit 1
}
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
sed -n '/^def spaceRanges : List (Nat × Nat) := \[$/,/^]$/p' verification/LabelCheckModel.lean | sed '1d;$d' > "$work/space-committed"
diff -u "$work/space" "$work/space-committed"

# 4. The probe: the real functions, and the module under another name for
# the functions it does not export.
sed -e 's/^module Peg.Grammar.Labels$/module LabelsInternal where/' -e '/^  ( labelWarnings$/,/^  ) where$/d' \
  "$source_file" > "$work/LabelsInternal.hs"
run_probe() {
  "${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-grammar -package=directory -package=filepath \
    --ghc-arg=-i"$work" --ghc-arg=-Wall --ghc-arg=-Werror verification/LabelCheckProbe.hs "$1"
}
run_probe lean > "$work/LabelCheckProbeCases.lean"
run_probe expect > "$work/haskell-output"

(cd verification &&
  LEAN_PATH="$work:$lean_objects" lean -DwarningAsError=true -R "$work" \
    -o "$work/LabelCheckProbeCases.olean" "$work/LabelCheckProbeCases.lean" &&
  LEAN_PATH="$work:$lean_objects" lean -DwarningAsError=true \
    --run LabelCheckProbe.lean > "$work/lean-output")

diff -u "$work/haskell-output" "$work/lean-output"
printf 'Label check: %s grammars, %s warnings agree.\n' \
  "$(grep -c '^case ' "$work/lean-output")" "$(grep -c '^warning ' "$work/lean-output")"
