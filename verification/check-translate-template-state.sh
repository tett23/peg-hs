#!/bin/sh
# root ADR 0097 I2: state transitions in the actual Templates.instanceOf.
set -eu
cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of compiled Lean modules}
ghc=${GHC:-ghc-9.10.3}
[ "$("$ghc" --numeric-version)" = 9.10.3 ] || exit 1
libdir=$("$ghc" --print-libdir)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
mkdir -p "$work/build"
"$ghc" -package ghc -O0 -Wall -Werror -Wno-incomplete-record-updates \
  -outputdir "$work/build" verification/TranslateHaskell.hs -o "$work/translate" \
  > "$work/build.log" 2>&1 || { cat "$work/build.log" >&2; exit 1; }
translate() {
  "$work/translate" "$libdir" "$1" "$1/Peg/Grammar/Templates.hs" \
    TemplateStateTranslated verification/translate-template-state.hints expandOnce.instanceOf
}
compile() {
  (cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
    -R "$(dirname "$1")" -o "$lean_objects/$(basename "$1" .lean).olean" "$1")
}
translate packages/peg-grammar/src > "$lean_objects/TemplateStateTranslated.lean"
compile "$lean_objects/TemplateStateTranslated.lean"
compile "$PWD/verification/TemplateStateProof.lean"

: > "$work/empty.hints"
"$work/translate" "$libdir" verification verification/TemplateMapProbe.hs \
  TemplateMapTranslated "$work/empty.hints" inserted other > "$lean_objects/TemplateMapTranslated.lean"
compile "$lean_objects/TemplateMapTranslated.lean"
cat > "$work/MapRun.hs" <<'HS'
{-# LANGUAGE OverloadedStrings #-}
import TemplateMapProbe
main :: IO ()
main = mapM_ print [inserted "a" 7 [], inserted "a" 7 [("a",2)],
  inserted "a" 7 [("a",2),("a",3)], other "b" "a" 7 [("b",9)], other "b" "a" 7 []]
HS
runghc-9.10.3 -iverification "$work/MapRun.hs" > "$work/expected"
cat > "$lean_objects/TemplateMapRun.lean" <<'LEAN'
import TemplateMapTranslated
open TemplateMapTranslated
def main : IO Unit := do
  for value in [inserted "a" 7 [], inserted "a" 7 [("a",2)],
      inserted "a" 7 [("a",2),("a",3)], other "b" "a" 7 [("b",9)], other "b" "a" 7 []] do
    IO.println value
LEAN
(cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
  --run "$lean_objects/TemplateMapRun.lean") > "$work/actual"
diff -u "$work/expected" "$work/actual"

cp -R packages/peg-grammar/src "$work/grammar"
for mutation in decrement double; do
  case "$mutation" in
    decrement) replacement='stCount = stCount st - 1' ;;
    double) replacement='stCount = stCount st + 2' ;;
  esac
  sed "s/stCount = stCount st + 1/$replacement/" packages/peg-grammar/src/Peg/Grammar/Templates.hs \
    > "$work/grammar/Peg/Grammar/Templates.hs"
  cmp -s packages/peg-grammar/src/Peg/Grammar/Templates.hs "$work/grammar/Peg/Grammar/Templates.hs" && exit 1
  translate "$work/grammar" > "$lean_objects/TemplateStateTranslated.lean"
  compile "$lean_objects/TemplateStateTranslated.lean"
  if compile "$PWD/verification/TemplateStateProof.lean" > "$work/rejected-$mutation.log" 2>&1; then
    echo "root ADR 0097 I2: accepted count $mutation" >&2; exit 1
  fi
  grep -E 'TemplateStateProof.lean:[0-9]+:[0-9]+: error:' "$work/rejected-$mutation.log" > /dev/null || {
    cat "$work/rejected-$mutation.log" >&2; exit 1;
  }
done
translate packages/peg-grammar/src > "$lean_objects/TemplateStateTranslated.lean"
compile "$lean_objects/TemplateStateTranslated.lean"
compile "$PWD/verification/TemplateStateProof.lean"
echo 'root ADR 0097 I2: instanceOf state proved; map insertion compared with GHC; 2 mutants rejected.'
