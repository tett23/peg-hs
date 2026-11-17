#!/bin/sh
# Ties AssembleChars, AssemblePredicates and AssembleBindings to
# Peg.Grammar.Assemble. Pass the directory that holds the compiled Lean
# modules (check.sh's work directory).
set -eu

cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of the compiled Lean modules}
source_file=packages/peg-grammar/src/Peg/Grammar/Assemble.hs
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# 1. The character tables are the extractor's output for GHC 9.10.3.
[ "$(ghc-9.10.3 --numeric-version)" = 9.10.3 ] || {
  echo 'GHC 9.10.3 is required for the Unicode tables.' >&2
  exit 1
}
[ "$(git hash-object verification/ExtractAssembleChars.hs)" = 8a2338e1311247b86d829122dbcd47dad732ebc6 ]
runghc-9.10.3 verification/ExtractAssembleChars.hs > "$work/ranges"
sed -n '/^def [a-zA-Z]*Ranges : List (Nat × Nat) := \[$/,/^]$/p' \
  verification/AssembleChars.lean > "$work/committed"
diff -u "$work/ranges" "$work/committed"

# 2. The Haskell sources that AssemblePredicates and AssembleBindings
# translate. A change to any of them requires reviewing the translation.
sed -n '/^isIdentStart ::/,/^  Nothing -> False$/p' "$source_file" > "$work/ident-span"
[ "$(git hash-object "$work/ident-span")" = d8d4fd4cb1f8c6e7ddf4c52a1e669cc6ca62ac63 ]
sed -n '/^    languageOptions =$/,/^      | otherwise = Nothing$/p' "$source_file" > "$work/binder-span"
[ "$(git hash-object "$work/binder-span")" = bda277531d4cf6510a5ab30249bfd3f4793ba3fc ]
sed -n '/^        ++ \[ Diagnostic (itemLoc i) ("binding name "/,/^           \]$/p' "$source_file" > "$work/binding-diagnostic"
sed -n '/^        ++ \[ Diagnostic al ("parameter name "/,/^           \]$/p' "$source_file" >> "$work/binding-diagnostic"
sed -n '/^    nestedItems i =/,/^      _ -> \[\]$/p' "$source_file" >> "$work/binding-diagnostic"
[ "$(git hash-object "$work/binding-diagnostic")" = 771748685a09336c0f5e8e96fb242523b1cefec0 ]
sed -n '/^isExtensionName ::/,/^-- Split export items/p' "$source_file" | sed '$d' > "$work/export-span"
[ "$(git hash-object "$work/export-span")" = 3c60e6860127ff607765bf4f61c164de971bf9d2 ]
sed -n '/^splitExports ::/,$p' "$source_file" > "$work/split-span"

# 3. Run the Haskell spans and the Lean translation on the same inputs.
cat > "$work/Probe.hs" <<'SOURCE'
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where
import Control.Applicative ((<|>))
import Data.Char (GeneralCategory (ModifierLetter), generalCategory, isAlphaNum, isAscii, isAsciiUpper, isUpper, ord)
import Data.List (intercalate, nub, sort)
import Data.Maybe (isJust, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Assemble (Top (..), assemble, isIdentChar, isValidIdent)
import System.Environment (getArgs)
import System.Exit (die)
import System.IO (hSetEncoding, stdout, utf8)
SOURCE
cat "$work/export-span" "$work/split-span" >> "$work/Probe.hs"
sed -e "/^--BINDER-SPAN--$/{r $work/binder-span" -e 'd' -e '}' \
  verification/AssemblePredicatesProbe.hs >> "$work/Probe.hs"

run_probe() {
  "${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-grammar \
    --ghc-arg=-Werror --ghc-arg=-Wincomplete-patterns "$work/Probe.hs" "$1"
}
run_probe lean > "$work/AssembleProbeCases.lean"
run_probe expected > "$work/haskell-output"

(cd verification &&
  LEAN_PATH="$work:$lean_objects" lean -DwarningAsError=true -R "$work" \
    -o "$work/AssembleProbeCases.olean" "$work/AssembleProbeCases.lean" &&
  LEAN_PATH="$work:$lean_objects" lean -DwarningAsError=true \
    --run AssemblePredicatesProbe.lean > "$work/lean-output")

diff -u "$work/haskell-output" "$work/lean-output"
printf 'Assemble predicates: 4 character tables over 1112064 scalar values; %s probe lines agree.\n' \
  "$(wc -l < "$work/lean-output" | tr -d ' ')"
