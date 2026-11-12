#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Assemble.hs}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# Pin both extracted implementations. If either changes, review the Lean
# translation before accepting its differential probe again.
sed -n '/^stringArg ::/,/^-- | Check the top-level items/p' "$source_file" |
  sed '$d' > "$work/string-source"
[ "$(git hash-object --stdin < "$work/string-source")" = 7ec899f82811410c0094a255a0afc5fd172da500 ]
sed -n '/^splitExports ::/,$p' "$source_file" > "$work/split-source"
[ "$(git hash-object --stdin < "$work/split-source")" = 50ccd5b08e64f1eb609bc9b84a227896c35012ce ]

cat > "$work/Probe.hs" <<'SOURCE'
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where
import Data.Char (chr, digitToInt, isHexDigit, isSpace)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar (Diagnostic (..), Loc (..), Located (..))
import Peg.Grammar.Assemble (advanceLoc, isValidIdent)
SOURCE
cat "$work/string-source" "$work/split-source" \
  verification/AssembleValidationHelpersProbe.hs >> "$work/Probe.hs"

"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -ipackages/peg-grammar/src \
  -package=peg-grammar "$work/Probe.hs" > "$work/haskell-output"

(cd verification &&
  LEAN_PATH="$work" lean -o "$work/Parsing.olean" Parsing.lean > /dev/null &&
  LEAN_PATH="$work" lean -o "$work/Lexical.olean" Lexical.lean > /dev/null &&
  LEAN_PATH="$work" lean -o "$work/Whitespace.olean" Whitespace.lean > /dev/null &&
  LEAN_PATH="$work" lean -o "$work/AssembleValidationHelpers.olean" AssembleValidationHelpers.lean > /dev/null &&
  LEAN_PATH="$work" lean --run AssembleValidationHelpersProbe.lean > "$work/lean-output")

diff -u "$work/haskell-output" "$work/lean-output"
printf 'Compared %s split/string boundary cases.\n' "$(wc -l < "$work/lean-output" | tr -d ' ')"
