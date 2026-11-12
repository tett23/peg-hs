#!/bin/sh
set -eu

source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Import.hs}
actual=$(awk '
  /^reachable :: \[Rule\] -> \[Text\] -> S.Set Text$/ { copying = 1 }
  copying && /^$/ { exit }
  copying { print }
' "$source_file")
expected='reachable :: [Rule] -> [Text] -> S.Set Text
reachable rules = go S.empty
  where
    byName = M.fromList [(ruleName r, r) | r <- rules]
    go seen = \case
      [] -> seen
      n : ns
        | S.member n seen -> go seen ns
        | otherwise -> go (S.insert n seen) (maybe [] ruleRefs (M.lookup n byName) ++ ns)'
if [ "$actual" != "$expected" ]; then
  echo 'The Haskell reachability algorithm changed; update its Lean model.' >&2
  exit 1
fi
