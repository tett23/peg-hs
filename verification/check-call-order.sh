#!/bin/sh
set -eu
scratch=${1:?pass the verification scratch directory}
extract_order() {
  "${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-grammar verification/ExtractCallOrder.hs "$@"
}
extract_order packages/peg-grammar/grammar/Peg.hpeg packages/peg-grammar/grammar/PegSyntax.hpeg > "$scratch/CallTables.lean"
(cd verification && lean -DwarningAsError=true -R "$scratch" -o "$scratch/CallTables.olean" "$scratch/CallTables.lean")
# Ordinary right recursion consumes a character. With the literal removed,
# the same recursive call is reachable before any input has been consumed.
for prefix in "'x'" "''"; do
  printf '%%module Recursive\nStart <- %s Start / .\n' "$prefix" > "$scratch/Recursive.hpeg"
  extract_order "$scratch/Recursive.hpeg" > "$scratch/Recursive.lean"
  if [ "$prefix" = "'x'" ]; then
    (cd verification && lean -DwarningAsError=true "$scratch/Recursive.lean")
  elif (cd verification && lean "$scratch/Recursive.lean") > "$scratch/order-error" 2>&1; then
    echo 'invariant1: accepted recursion without progress' >&2
    exit 1
  else
    grep -Fq 'Tactic `decide` proved that the proposition' "$scratch/order-error"
  fi
done
