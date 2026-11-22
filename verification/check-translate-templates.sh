#!/bin/sh
# root ADR 0097 I2: translate the whole template pass, prove its state/error
# properties, and compare all output fields with the actual public entry.
set -eu
cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of compiled Lean modules}
ghc=${GHC:-ghc-9.10.3}
cabal=${CABAL:-cabal}
[ "$("$ghc" --numeric-version)" = 9.10.3 ] || exit 1
libdir=$("$ghc" --print-libdir)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
mkdir -p "$work/build"
"$ghc" -package ghc -O0 -Wall -Werror -Wno-incomplete-record-updates \
  -outputdir "$work/build" verification/TranslateHaskell.hs -o "$work/translate" \
  > "$work/build.log" 2>&1 || { cat "$work/build.log" >&2; exit 1; }
compile() {
  (cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
    -R "$(dirname "$1")" -o "$lean_objects/$(basename "$1" .lean).olean" "$1")
}
translate() {
  "$work/translate" "$libdir" "$1" "$1/Peg/Grammar/Templates.hs" \
    TemplatesTranslated verification/translate-templates.hints expandTemplates
}
translate packages/peg-grammar/src > "$lean_objects/TemplatesTranslated.lean"
compile "$lean_objects/TemplatesTranslated.lean"
compile "$PWD/verification/TemplatesTranslatedProof.lean"
compile "$PWD/verification/TemplateCollectionsProof.lean"

# Reuse the same eleven grammars as the model's probe, without copying its
# projection: Generic serialization writes every field, including types.
grep -Fqx 'module Main (main) where' verification/TemplateExpansionWholeProbe.hs
sed 's/module Main (main) where/module TemplateCases where/' verification/TemplateExpansionWholeProbe.hs \
  > "$work/TemplateCases.hs"
"$cabal" exec -v0 -- runghc-9.10.3 -Wall -Werror -package=peg-grammar -i"$work" \
  verification/TemplatesTranslatedProbe.hs > "$lean_objects/TemplatesRun.lean"
(cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
  --run "$lean_objects/TemplatesRun.lean")

# The collection operations used by the full pass, including extensional
# show equality for maps and sets constructed in different orders.
: > "$work/empty.hints"
"$work/translate" "$libdir" verification verification/TemplateCollectionsProbe.hs \
  TemplateCollectionsTranslated "$work/empty.hints" unionValues mappedValues intersectionValues deduplicated flags \
  > "$lean_objects/TemplateCollectionsTranslated.lean"
compile "$lean_objects/TemplateCollectionsTranslated.lean"
cat > "$work/CollectionsRun.hs" <<'HS'
{-# LANGUAGE OverloadedStrings #-}
import TemplateCollectionsProbe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
rows :: [(Text,Integer)] -> IO ()
rows values = do
  print (length values)
  mapM_ (\(key,value) -> T.putStrLn (key <> ":" <> T.pack (show value))) values
texts :: [Text] -> IO ()
texts values = print (length values) >> mapM_ T.putStrLn values
main :: IO ()
main = do
  mapM_ (rows . uncurry unionValues)
    [([],[]),([] ,[("a",2)]), ([("a",1)],[]),
     ([("a",1),("z",9)],[("a",2),("b",3)]), ([("a",1),("a",4)],[("a",2)])]
  mapM_ (rows . mappedValues) [[],[("空",1),("a",-20)]]
  mapM_ (texts . uncurry intersectionValues)
    [([],["a"]),(["a"],[]),(["b","a"],["a","b"]),(["空","a","空"],["空"])]
  mapM_ (texts . deduplicated) [[],["b","a","b","空","a"]]
  mapM_ (print . (\b -> if b then (1 :: Integer) else 0)) flags
HS
runghc-9.10.3 -iverification "$work/CollectionsRun.hs" > "$work/expected"
cat > "$lean_objects/CollectionsRun.lean" <<'LEAN'
import TemplateCollectionsTranslated
open TemplateCollectionsTranslated
def rows (values : List (String × Int)) : IO Unit := do
  IO.println values.length
  for (key,value) in values do IO.println s!"{key}:{value}"
def texts (values : List String) : IO Unit := do
  IO.println values.length
  for value in values do IO.println value
def main : IO Unit := do
  for (left,right) in [([],[]),([] ,[("a",2)]), ([("a",1)],[]),
      ([("a",1),("z",9)],[("a",2),("b",3)]), ([("a",1),("a",4)],[("a",2)])] do
    rows (unionValues left right)
  for values in [[],[("空",1),("a",-20)]] do rows (mappedValues values)
  for (left,right) in [([],["a"]),(["a"],[]),(["b","a"],["a","b"]),(["空","a","空"],["空"])] do
    texts (intersectionValues left right)
  for values in [[],["b","a","b","空","a"]] do texts (deduplicated values)
  for b in flags do IO.println (if b then (1 : Int) else 0)
LEAN
(cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true \
  --run "$lean_objects/CollectionsRun.lean") > "$work/actual"
diff -u "$work/expected" "$work/actual"

# Change supported, well-typed semantics. Rejection must come from the
# proved properties, not a source hash, parser error or missing import.
for mutation in intersection union; do
  mutant="$work/$mutation"
  mkdir -p "$mutant"
  case "$mutation" in
    intersection) sed 's/a.elems.filter (member · b)/a.elems.filter (fun x => !member x b)/' \
      verification/HsPrelude.lean > "$mutant/HsPrelude.lean" ;;
    union) sed 's/if member p.1 result then result else insert p.1 p.2 result/insert p.1 p.2 result/' \
      verification/HsPrelude.lean > "$mutant/HsPrelude.lean" ;;
  esac
  cmp -s verification/HsPrelude.lean "$mutant/HsPrelude.lean" && exit 1
  (cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true -R "$mutant" \
    -o "$mutant/HsPrelude.olean" "$mutant/HsPrelude.lean")
  if (cd verification && LEAN_PATH="$mutant:$lean_objects" lean -DwarningAsError=true \
    TemplateCollectionsProof.lean) > "$mutant/rejected.log" 2>&1; then
    echo "root ADR 0097 I2: accepted changed collection $mutation" >&2; exit 1
  fi
  grep -E 'TemplateCollectionsProof.lean:[0-9]+:[0-9]+: error:' "$mutant/rejected.log" > /dev/null
  grep -E 'error: (Type mismatch|Application type mismatch|unsolved goals|Tactic)' "$mutant/rejected.log" > /dev/null || {
    cat "$mutant/rejected.log" >&2; exit 1;
  }
done
cp -R packages/peg-grammar/src "$work/grammar"
# Keep the original child dependency and add the parent to the recursive
# traversal. The size proof must reject this well-typed infinite recursion.
sed 's/x -> concatMap exprCode (exprChildren x)/x -> concatMap exprCode (x : exprChildren x)/' \
  packages/peg-grammar/src/Peg/Grammar/Templates.hs > "$work/grammar/Peg/Grammar/Templates.hs"
cmp -s packages/peg-grammar/src/Peg/Grammar/Templates.hs "$work/grammar/Peg/Grammar/Templates.hs" && exit 1
translate "$work/grammar" > "$lean_objects/TemplatesTranslated.lean"
if compile "$lean_objects/TemplatesTranslated.lean" > "$work/code-loop-rejected.log" 2>&1; then
  echo 'root ADR 0097 I2: accepted non-decreasing exprCode recursion' >&2; exit 1
fi
grep -E 'TemplatesTranslated.lean:[0-9]+:[0-9]+: error: Tactic' "$work/code-loop-rejected.log" > /dev/null || {
  cat "$work/code-loop-rejected.log" >&2; exit 1;
}
if grep -E 'unknownIdentifier|unknown module|Function expected at' "$work/code-loop-rejected.log" > /dev/null; then
  cat "$work/code-loop-rejected.log" >&2; exit 1
fi
# Recur on the same expression instead of its child. GHC still accepts the
# definition; the translation must fail its kernel-checked size decrease.
sed 's/EStar x -> EStar (plain x)/EStar x -> EStar (plain (EStar x))/' \
  packages/peg-grammar/src/Peg/Grammar/Templates.hs > "$work/grammar/Peg/Grammar/Templates.hs"
cmp -s packages/peg-grammar/src/Peg/Grammar/Templates.hs "$work/grammar/Peg/Grammar/Templates.hs" && exit 1
translate "$work/grammar" > "$lean_objects/TemplatesTranslated.lean"
if compile "$lean_objects/TemplatesTranslated.lean" > "$work/plain-loop-rejected.log" 2>&1; then
  echo 'root ADR 0097 I2: accepted non-decreasing plain recursion' >&2; exit 1
fi
grep -E 'TemplatesTranslated.lean:[0-9]+:[0-9]+: error: Tactic' "$work/plain-loop-rejected.log" > /dev/null || {
  cat "$work/plain-loop-rejected.log" >&2; exit 1;
}
sed 's/Left (nub (reverse errs))/Left []/' packages/peg-grammar/src/Peg/Grammar/Templates.hs \
  > "$work/grammar/Peg/Grammar/Templates.hs"
cmp -s packages/peg-grammar/src/Peg/Grammar/Templates.hs "$work/grammar/Peg/Grammar/Templates.hs" && exit 1
translate "$work/grammar" > "$lean_objects/TemplatesTranslated.lean"
compile "$lean_objects/TemplatesTranslated.lean"
if compile "$PWD/verification/TemplatesTranslatedProof.lean" > "$work/empty-errors-rejected.log" 2>&1; then
  echo 'root ADR 0097 I2: accepted empty template diagnostics' >&2; exit 1
fi
grep -E 'TemplatesTranslatedProof.lean:[0-9]+:[0-9]+: error:' "$work/empty-errors-rejected.log" > /dev/null
grep -E 'error: (Type mismatch|Application type mismatch|unsolved goals|Tactic)' "$work/empty-errors-rejected.log" > /dev/null || {
  cat "$work/empty-errors-rejected.log" >&2; exit 1;
}
translate packages/peg-grammar/src > "$lean_objects/TemplatesTranslated.lean"
compile "$lean_objects/TemplatesTranslated.lean"
compile "$PWD/verification/TemplatesTranslatedProof.lean"
echo 'root ADR 0097 I2: whole template translation, state/error proofs and 5 mutants checked.'
