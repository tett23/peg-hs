#!/bin/sh
# root ADR 0097 I2: head demand on a filtered infinite Integer enumeration.
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
  "$work/translate" "$libdir" "$1" "$1/InfiniteHeadProbe.hs" \
    InfiniteHeadTranslated "$2" firstFree firstName
}
compile() {
  (cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
    -R "$(dirname "$1")" -o "$lean_objects/$(basename "$1" .lean).olean" "$1")
}
translate verification verification/translate-infinite-head.hints > "$lean_objects/InfiniteHeadTranslated.lean"
compile "$lean_objects/InfiniteHeadTranslated.lean"
compile "$PWD/verification/InfiniteHeadProof.lean"

: > "$work/empty.hints"
# Implicit methods used by a do-block's default (>>) remain dependencies
# when the requested root is a local function.
"$work/translate" "$libdir" verification verification/LocalRootProbe.hs \
  LocalRootTranslated "$work/empty.hints" outer.local > "$lean_objects/LocalRootTranslated.lean"
compile "$lean_objects/LocalRootTranslated.lean"
cat > "$lean_objects/LocalRootCheck.lean" <<'LEAN'
import LocalRootTranslated
example (x : Int) : LocalRootTranslated.outer.local__14 x = LocalRootTranslated.Box.Box x := by rfl
LEAN
compile "$lean_objects/LocalRootCheck.lean"

"$work/translate" "$libdir" verification verification/TemplateLibraryProbe.hs \
  TemplateLibraryTranslated "$work/empty.hints" numbers flags texts scanned dropped ascending \
  > "$lean_objects/TemplateLibraryTranslated.lean"
compile "$lean_objects/TemplateLibraryTranslated.lean"
cat > "$work/LibraryRun.hs" <<'HS'
import TemplateLibraryProbe
import qualified Data.Text.IO as T
main :: IO ()
main = do
  mapM_ print (numbers ++ scanned ++ dropped)
  mapM_ (print . (\b -> if b then (1 :: Integer) else 0)) flags
  mapM_ T.putStrLn (texts ++ ascending)
HS
runghc-9.10.3 -iverification "$work/LibraryRun.hs" > "$work/library-expected"
cat > "$lean_objects/TemplateLibraryRun.lean" <<'LEAN'
import TemplateLibraryTranslated
open TemplateLibraryTranslated
def main : IO Unit := do
  for n in numbers ++ scanned ++ dropped do IO.println n
  for b in flags do IO.println (if b then (1 : Int) else 0)
  for t in texts ++ ascending do IO.println t
LEAN
(cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
  --run "$lean_objects/TemplateLibraryRun.lean") > "$work/library-actual"
diff -u "$work/library-expected" "$work/library-actual"

cat > "$work/Probe.hs" <<'HS'
{-# LANGUAGE OverloadedStrings #-}
import InfiniteHeadProbe
import qualified Data.Set as S
import qualified Data.Text.IO as T
main :: IO ()
main = do
  mapM_ (print . uncurry firstFree)
    [(0, []), (0, [0,1,2]), (-3, [-3,-2]), (2^100, [2^100,2^100+1]), (0, [0,0,1])]
  mapM_ (\(b,n,u,g) -> T.putStrLn (firstName b n (S.fromList u) (S.fromList g)))
    [("A",0,[],[]), ("A",0,["A'0"],["A'1"]), ("A'",7,["A''7"],[]), ("空",0,[],[])]
HS
runghc-9.10.3 -iverification "$work/Probe.hs" > "$work/expected"
cat > "$lean_objects/InfiniteHeadRun.lean" <<'LEAN'
import InfiniteHeadTranslated
open InfiniteHeadTranslated
example : firstFree 1 0 [0] = 0 := by decide
example : firstFree 0 0 [] = 0 := by decide
example : firstFree 2 0 [] = 0 := by decide
example : firstFree 5 0 [0,1,2] = 3 := by decide
example : firstFree 5 0 [0,1,2,3] = 0 := by decide
example : firstFree 6 0 [0,1,2,3] = 4 := by decide

def main : IO Unit := do
  for (n,u) in [(0, []), (0, [0,1,2]), (-3, [-3,-2]),
      (2^100, [2^100,2^100+1]), (0, [0,0,1])] do
    IO.println (firstFree 16 n u)
  for (b,n,u,g) in [("A",0,[],[]), ("A",0,["A'0"],["A'1"]),
      ("A'",7,["A''7"],[]), ("空",0,[],[])] do
    IO.println (firstName 16 b n (HsSet.fromList u) (HsSet.fromList g))
LEAN
(cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
  --run "$lean_objects/InfiniteHeadRun.lean") > "$work/actual"
diff -u "$work/expected" "$work/actual"

# Unsupported consumers and Enum instances must be rejected, not truncated.
mkdir -p "$work/mutant"
reject() {
  if translate "$work/mutant" "$1" > "$work/rejected.lean" 2> "$work/rejected.log"; then
    echo "root ADR 0097 I2: accepted unsupported infinite search: $2" >&2; exit 1
  fi
  grep -F "$2" "$work/rejected.log" > /dev/null || { cat "$work/rejected.log" >&2; exit 1; }
}
sed 's/c : _ -> c/c : rest -> c + fromIntegral (length rest)/' verification/InfiniteHeadProbe.hs \
  | sed '/firstName ::/,$d' > "$work/mutant/InfiniteHeadProbe.hs"
# Keep firstName as a root without introducing another unsupported use.
cat >> "$work/mutant/InfiniteHeadProbe.hs" <<'HS'
firstName :: Integer
firstName = 0
HS
reject verification/translate-infinite-head.hints 'unsupported: an infinite enumeration whose tail is inspected'
sed 's/firstFree :: Integer -> \[Integer\] -> Integer/firstFree :: Int -> [Int] -> Int/' \
  verification/InfiniteHeadProbe.hs > "$work/mutant/InfiniteHeadProbe.hs"
reject verification/translate-infinite-head.hints 'unsupported: an infinite enumeration at a type other than Integer'
cp verification/InfiniteHeadProbe.hs "$work/mutant/InfiniteHeadProbe.hs"
reject "$work/empty.hints" 'unsupported: an infinite head search without a fuel hint'

# A supported semantic change must fail the actual universal proof.
sed 's/not (S.member c used)/S.member c used/' verification/InfiniteHeadProbe.hs \
  > "$work/mutant/InfiniteHeadProbe.hs"
translate "$work/mutant" verification/translate-infinite-head.hints > "$lean_objects/InfiniteHeadTranslated.lean"
compile "$lean_objects/InfiniteHeadTranslated.lean"
if compile "$PWD/verification/InfiniteHeadProof.lean" > "$work/proof-rejected.log" 2>&1; then
  echo 'root ADR 0097 I2: accepted reversed freshness predicate' >&2; exit 1
fi
grep -E 'InfiniteHeadProof.lean:[0-9]+:[0-9]+: error:' "$work/proof-rejected.log" > /dev/null || {
  cat "$work/proof-rejected.log" >&2; exit 1;
}
translate verification verification/translate-infinite-head.hints > "$lean_objects/InfiniteHeadTranslated.lean"
compile "$lean_objects/InfiniteHeadTranslated.lean"
compile "$PWD/verification/InfiniteHeadProof.lean"

# Translate the actual local definition, with its lexical environment kept
# explicit. The proof checks it against the probe for every fuel and input.
fresh() {
  "$work/translate" "$libdir" "$1" "$1/Peg/Grammar/Templates.hs" \
    TemplateFreshTranslated verification/translate-template-fresh.hints expandOnce.freshName
}
fresh packages/peg-grammar/src > "$lean_objects/TemplateFreshTranslated.lean"
compile "$lean_objects/TemplateFreshTranslated.lean"
compile "$PWD/verification/TemplateFreshProof.lean"
if "$work/translate" "$libdir" packages/peg-grammar/src packages/peg-grammar/src/Peg/Grammar/Templates.hs \
  TemplateFreshTranslated verification/translate-template-fresh.hints expandOnce.noSuchFunction \
  > "$work/missing-root.lean" 2> "$work/missing-root.log"; then
  echo 'root ADR 0097 I2: accepted nonexistent local root' >&2; exit 1
fi
grep -F 'no matching function root' "$work/missing-root.log" > /dev/null || {
  cat "$work/missing-root.log" >&2; exit 1;
}
cat > "$work/Ambiguous.hs" <<'HS'
module Ambiguous where
outer :: Integer -> Integer
outer x = let same y = y in same (let same z = z + 1 in same x)
HS
if "$work/translate" "$libdir" "$work" "$work/Ambiguous.hs" AmbiguousTranslated \
  "$work/empty.hints" outer.same > "$work/ambiguous.lean" 2> "$work/ambiguous.log"; then
  echo 'root ADR 0097 I2: accepted ambiguous local root' >&2; exit 1
fi
grep -F 'ambiguous local function root outer.same' "$work/ambiguous.log" > /dev/null || {
  cat "$work/ambiguous.log" >&2; exit 1;
}
cp -R packages/peg-grammar/src "$work/grammar"
sed 's/not (S.member c usedNames)/S.member c usedNames/' \
  packages/peg-grammar/src/Peg/Grammar/Templates.hs > "$work/grammar/Peg/Grammar/Templates.hs"
cmp -s packages/peg-grammar/src/Peg/Grammar/Templates.hs "$work/grammar/Peg/Grammar/Templates.hs" && exit 1
fresh "$work/grammar" > "$lean_objects/TemplateFreshTranslated.lean"
compile "$lean_objects/TemplateFreshTranslated.lean"
if compile "$PWD/verification/TemplateFreshProof.lean" > "$work/fresh-rejected.log" 2>&1; then
  echo 'root ADR 0097 I2: accepted changed Templates.freshName' >&2; exit 1
fi
grep -E 'TemplateFreshProof.lean:[0-9]+:[0-9]+: error:' "$work/fresh-rejected.log" > /dev/null || {
  cat "$work/fresh-rejected.log" >&2; exit 1;
}
fresh packages/peg-grammar/src > "$lean_objects/TemplateFreshTranslated.lean"
compile "$lean_objects/TemplateFreshTranslated.lean"
compile "$PWD/verification/TemplateFreshProof.lean"
echo 'root ADR 0097 I2: actual freshName proved; GHC comparison and 7 negative checks passed.'
