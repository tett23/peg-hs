#!/bin/sh
set -eu

scratch=${1:?pass the verification scratch directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-grammar -package=mtl \
  verification/ExtractConcreteTerminals.hs \
  packages/peg-grammar/grammar/Peg.hpeg \
  packages/peg-grammar/grammar/PegSyntax.hpeg > "$scratch/ConcreteTables.lean"
[ "$(grep -c '^namespace MetaTerminal[12]$' "$scratch/ConcreteTables.lean")" -eq 2 ]
[ "$(grep -c '^-- counts ' "$scratch/ConcreteTables.lean")" -eq 2 ]
(cd verification &&
  lean -DwarningAsError=true -o "$scratch/ConcreteTerminal.olean" ConcreteTerminal.lean &&
  lean -DwarningAsError=true -o "$scratch/Utf8Terminals.olean" Utf8Terminals.lean &&
  lean -DwarningAsError=true -o "$scratch/ConcreteTerminalBody.olean" ConcreteTerminalBody.lean &&
  lean -DwarningAsError=true -R "$scratch" -o "$scratch/ConcreteTables.olean" "$scratch/ConcreteTables.lean")
