#!/bin/sh
set -eu

: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

for grammar in Peg PegSyntax; do
  source="packages/peg-grammar/grammar/$grammar.hpeg"
  [ "$(grep -c '^Ws <-' "$source")" -eq 1 ]
  [ "$(grep -c '^SpaceChar <-' "$source")" -eq 1 ]
  [ "$(grep -c '^Comment <-' "$source")" -eq 1 ]
  grep -Fqx 'Ws <- (SpaceChar / Comment)*' "$source"
  grep -Fqx 'SpaceChar <- c:$. &{ isSpace (firstChar c) } { () }' "$source"
  grep -Fqx "Comment <- '#' (!'\n' .)*" "$source"
  grep -Fqx 'firstChar = T.foldr const '\'' '\''' "$source"
done

(cd verification && lean -DwarningAsError=true --run WhitespaceScalars.lean) > "$LEAN_PATH/whitespace-lean.txt"
"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=base \
  verification/WhitespaceProbe.hs > "$LEAN_PATH/whitespace-ghc.txt"
cmp "$LEAN_PATH/whitespace-lean.txt" "$LEAN_PATH/whitespace-ghc.txt"
