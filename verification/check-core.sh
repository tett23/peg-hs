#!/bin/sh
set -eu

scratch=${1:?pass the shared temporary directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"
: "${CABAL:=cabal}"

[ -f "$LEAN_PATH/Parsing.olean" ] || {
  echo 'Parsing.olean is missing' >&2
  exit 1
}

(cd verification && lean --run CoreProbe.lean) > "$scratch/core-lean.txt"
"$CABAL" exec --with-compiler=ghc-9.10.3 -- \
  sh -c 'runghc-9.10.3 -XRankNTypes -package=peg-runtime verification/CoreProbe.hs > "$1"' \
  sh "$scratch/core-haskell.txt"

diff -u "$scratch/core-haskell.txt" "$scratch/core-lean.txt"
cat "$scratch/core-lean.txt"
