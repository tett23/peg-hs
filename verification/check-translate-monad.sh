#!/bin/sh
# root ADR 0097 I2: use GHC's actual Monad methods and list traversals.
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
: > "$work/empty.hints"
compile() {
  (cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
    -R "$(dirname "$1")" -o "$lean_objects/$(basename "$1" .lean).olean" "$1")
}
translate() {
  source=$1
  namespace=$2
  shift 2
  "$work/translate" "$libdir" "$(dirname "$source")" "$source" "$namespace" "$work/empty.hints" "$@" \
    > "$lean_objects/$namespace.lean"
  compile "$lean_objects/$namespace.lean"
}
library() {
  translate "$1" MonadLibraryTranslated defaultDo defaultOperator mapped mappedBase mapped_ emptyMapped_ filtered
}
library verification/MonadLibraryProbe.hs
translate verification/MonadOverrideProbe.hs MonadOverrideTranslated overrideDo overrideOperator overridden_
translate verification/MonadLiftProbe.hs MonadLiftTranslated mappedLift
compile "$PWD/verification/MonadMethodsProof.lean"

cat > "$work/Run.hs" <<'HS'
import qualified MonadLibraryProbe as D
import qualified MonadOverrideProbe as O
import qualified MonadLiftProbe as L
main :: IO ()
main = mapM_ print [D.defaultDo, D.defaultOperator, D.mapped, D.mappedBase, D.mapped_,
  D.emptyMapped_, O.overrideDo, O.overrideOperator, O.overridden_, L.mappedLift, D.filtered]
HS
runghc-9.10.3 -iverification "$work/Run.hs" > "$work/expected"
cat > "$lean_objects/MonadRun.lean" <<'LEAN'
import MonadLibraryTranslated
import MonadOverrideTranslated
import MonadLiftTranslated
def main : IO Unit := do
  for value in [MonadLibraryTranslated.defaultDo, MonadLibraryTranslated.defaultOperator,
      MonadLibraryTranslated.mapped, MonadLibraryTranslated.mappedBase,
      MonadLibraryTranslated.mapped_, MonadLibraryTranslated.emptyMapped_,
      MonadOverrideTranslated.overrideDo, MonadOverrideTranslated.overrideOperator,
      MonadOverrideTranslated.overridden_, MonadLiftTranslated.mappedLift, MonadLibraryTranslated.filtered] do
    IO.println value
LEAN
(cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
  --run "$lean_objects/MonadRun.lean") > "$work/actual"
diff -u "$work/expected" "$work/actual"

# The same syntax remains translatable when its evaluation changes; the
# universal default-sequence proof and the traversal proof must reject it.
mkdir -p "$work/mutant"
sed 's/Mark (n + m) b/Mark (n + m + 1) b/' verification/MonadLibraryProbe.hs \
  > "$work/mutant/MonadLibraryProbe.hs"
cmp -s verification/MonadLibraryProbe.hs "$work/mutant/MonadLibraryProbe.hs" && exit 1
library "$work/mutant/MonadLibraryProbe.hs"
if compile "$PWD/verification/MonadMethodsProof.lean" > "$work/rejected-bind.log" 2>&1; then
  echo 'root ADR 0097 I2: accepted changed Monad bind' >&2; exit 1
fi
grep -E 'MonadMethodsProof.lean:[0-9]+:[0-9]+: error:' "$work/rejected-bind.log" > /dev/null || {
  cat "$work/rejected-bind.log" >&2; exit 1;
}
library verification/MonadLibraryProbe.hs
sed 's/n + m + 50/n + m + 60/' verification/MonadLiftProbe.hs > "$work/mutant/MonadLiftProbe.hs"
cmp -s verification/MonadLiftProbe.hs "$work/mutant/MonadLiftProbe.hs" && exit 1
translate "$work/mutant/MonadLiftProbe.hs" MonadLiftTranslated mappedLift
if compile "$PWD/verification/MonadMethodsProof.lean" > "$work/rejected-lift.log" 2>&1; then
  echo 'root ADR 0097 I2: accepted changed Applicative liftA2' >&2; exit 1
fi
grep -E 'MonadMethodsProof.lean:[0-9]+:[0-9]+: error:' "$work/rejected-lift.log" > /dev/null || {
  cat "$work/rejected-lift.log" >&2; exit 1;
}
translate verification/MonadLiftProbe.hs MonadLiftTranslated mappedLift
compile "$PWD/verification/MonadMethodsProof.lean"
echo 'root ADR 0097 I2: Monad defaults, overrides and list traversals agree with GHC; 2 mutants rejected.'
