#!/bin/sh
set -eu
work=${1:?pass the Lean object directory}
cd "$(dirname "$0")"
runghc-9.10.3 ExtractSemanticClasses.hs > "$work/GhcPredicates.lean"
lean -DwarningAsError=true -R "$work" -o "$work/GhcPredicates.olean" "$work/GhcPredicates.lean"
