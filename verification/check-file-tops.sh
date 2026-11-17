#!/bin/sh
# ADR 0097 invariant 1, the value of parseTops (FileTops.lean). Pin the
# Haskell whose value FileTops models, then compare the items of the Lean
# model with the Top values that the real parseTops returns. Pass the
# directory of the compiled Lean modules (check.sh's work directory); it must
# hold FileTops.olean.
set -eu
cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of the compiled Lean modules}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# 1. The value of File is the list of many TopItem, TopItem returns the value
# of TopOne, and TopOne returns the value of the first alternative that
# succeeds (Chain, Chosen, fileValue). The LINE pragmas are left out: they
# move whenever Peg.hpeg changes above these rules.
sed -n "/^peg'rule'File =/,/^peg'rule'Here ::/p" packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs |
  sed '$d' | grep -v '^{-# LINE ' > "$work/rules"
[ "$(git hash-object "$work/rules")" = 46d59663cd9f88c96b1f04ee66bf18bdb15984cb ] || {
  echo 'review FileTops.lean: the generated File, TopItem or TopOne changed' >&2
  exit 1
}

# 2. many keeps the value of each call that succeeds with progress, in order,
# and stops at a failure or a success without progress (Chain).
sed -n '/^many :: /,/^   in go i \[\]$/p' packages/peg-runtime/src/Peg/Runtime/Internal.hs > "$work/many"
[ "$(git hash-object "$work/many")" = 05df7fce739553a77019e0214798480ac131e0d8 ] || {
  echo 'review FileTops.lean: Peg.Runtime.Internal.many changed' >&2
  exit 1
}

# 3. The probe: the kinds, the order, the number and the locations of the
# Top values, from the real parseTops and from runTops.
mkdir "$work/cases"
"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-grammar -package=directory \
  -package=filepath -package=bytestring -package=text \
  --ghc-arg=-Wall --ghc-arg=-Werror verification/FileTopsProbe.hs "$work/cases" > "$work/haskell"
(cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
  --run FileTopsProbe.lean "$work/cases/manifest") > "$work/lean"
diff -u "$work/haskell" "$work/lean"
printf 'File tops: %s files, %s accepted, %s items agree.\n' \
  "$(grep -c '^case ' "$work/lean")" "$(grep -c '^ok ' "$work/lean")" \
  "$(grep -cE '^(verbatim|directive|declaration) ' "$work/lean")"
