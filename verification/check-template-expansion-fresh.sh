#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Templates.hs}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

verification/check-template-expansion.sh "$source_file" packages/peg-grammar/src/Peg/Grammar.hs > /dev/null

# The lazy search and its Integer decimal suffix must remain this expression.
cat > "$work/expected" <<'SOURCE'
    freshName base n generated = case [c | k <- [n ..], let c = base <> "'" <> T.pack (show (k :: Integer)), not (S.member c usedNames), not (S.member c generated)] of
      c : _ -> c
      [] -> base
SOURCE
sed -n '/^    freshName base n generated =/,/^      \[\] -> base$/p' "$source_file" > "$work/source"
diff -u "$work/expected" "$work/source"
grep -Fqx '  , stCount :: Integer' "$source_file"
grep -Fqx '    usedNames = S.fromList (map ruleName (grammarRules g))' "$source_file"
grep -Fqx '          generated <- gets'"'"' stInstanceNames' "$source_file"

cat > "$work/Probe.hs" <<'SOURCE'
{-# LANGUAGE OverloadedStrings #-}
module Main where
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Set as S

probe :: [Text] -> [Text] -> Integer -> Text
probe original generated n = freshName "T" n (S.fromList generated)
  where
    usedNames = S.fromList original
SOURCE
cat "$work/source" verification/TemplateExpansionFreshProbe.hs >> "$work/Probe.hs"
"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=text -package=containers \
  "$work/Probe.hs" > "$work/haskell-output"

(cd verification &&
  LEAN_PATH="$work" lean -o "$work/TemplateSubstitution.olean" TemplateSubstitution.lean > /dev/null &&
  LEAN_PATH="$work" lean -o "$work/TemplateQueue.olean" TemplateQueue.lean > /dev/null &&
  LEAN_PATH="$work" lean -o "$work/TemplateExpansion.olean" TemplateExpansion.lean > /dev/null &&
  LEAN_PATH="$work" lean -o "$work/TemplateExpansionFresh.olean" TemplateExpansionFresh.lean > /dev/null &&
  LEAN_PATH="$work" lean --run TemplateExpansionFreshProbe.lean > "$work/lean-output")

diff -u "$work/haskell-output" "$work/lean-output"
printf 'Compared %s decimal suffix and fresh search cases.\n' "$(wc -l < "$work/lean-output" | tr -d ' ')"
