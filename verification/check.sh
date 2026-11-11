#!/bin/sh
# Run from any directory. The Lean modules are compiled into a fresh directory.
set -eu

cd "$(dirname "$0")"
toolchain=$(cat lean-toolchain)
version=$(lean --version)
case "$version" in
  "Lean (version ${toolchain#leanprover/lean4:v},"*) ;;
  *) echo "Expected $toolchain; found $version" >&2; exit 1 ;;
esac
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work"

for module in Guard Parsing Header; do
  lean -DwarningAsError=true -o "$work/$module.olean" "$module.lean"
done
lean -DwarningAsError=true Audit.lean
lean --run Boundary.lean > "$work/expected"
cd ..
verification/check-guard.sh
verification/check-header.sh
"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-codegen -package=peg-grammar verification/Boundary.hs > "$work/actual"
diff -u "$work/expected" "$work/actual"
verification/check-core.sh "$work"

# Regenerate both parsers from the actual grammar files, then ask GHC to read
# the exact emitted modules, including their user-supplied Haskell.
cabal=${CABAL:-cabal}
peg=$("$cabal" list-bin exe:peg-hs)
for grammar in Peg PegSyntax; do
  "$peg" gen "packages/peg-grammar/grammar/$grammar.hpeg" -o "$work/$grammar.hs"
  "$cabal" exec -- ghc-9.10.3 -fno-code -fforce-recomp -package peg-runtime \
    -package peg-grammar -outputdir "$work" "$work/$grammar.hs"
done
printf '%s\n' '%module Broken' 'S :: ()' "S <- 'a' { let }" > "$work/Broken.hpeg"
"$peg" gen "$work/Broken.hpeg" -o "$work/Broken.hs"
if "$cabal" exec -- ghc-9.10.3 -fno-code -package peg-runtime -outputdir "$work" \
  "$work/Broken.hs" > "$work/ghc-error" 2>&1; then
  echo 'invariant3: GHC unexpectedly accepted an incomplete expression' >&2
  exit 1
fi
grep -q 'parse error' "$work/ghc-error" || { cat "$work/ghc-error" >&2; exit 1; }
