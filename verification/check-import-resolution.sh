#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Import.hs}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# The source spans translated by ImportResolution.lean, step by step:
# resolveImports (readLibrary, readAll, partition, merge, kept), the
# reachability walk (reachableGo), the duplicate scan (duplicateDiagnostics)
# and the relocation of diagnostics (inFile). Any change fails closed and
# needs a review of the Lean model.
cat > "$work/expected" <<'SOURCE'
resolveImports :: Grammar -> [(FilePath, Text)] -> Either [Diagnostic] Grammar
resolveImports root texts
  | isJust (grammarLibrary root) = Left [Diagnostic (Loc 0 1 1) "missing %module directive"]
  | otherwise = case partitionEithers (zipWith library [1 ..] (grammarImports root)) of
      ([], libs) -> merge (grammarRules root ++ concat libs)
      (errs, _) -> Left (sortOn diagLoc (concat errs))
  where
    library i (Located l p) = case lookup p texts of
      Nothing -> Left [Diagnostic l ("cannot import " <> T.pack p <> ": no such file")]
      Just text -> case parseTops text of
        Left ds -> Left (map (inFile i) ds)
        Right tops
          | null [() | TDirective _ "library" _ _ <- tops] ->
              Left [Diagnostic l (T.pack p <> " is not a library: it has no %library directive")]
          | otherwise -> case assemble tops of
              Left ds -> Left (map (inFile i) ds)
              Right g -> case libraryErrors g of
                [] -> Right (map (relocateRule i) (grammarRules g))
                ds -> Left (map (inFile i) ds)
    merge rules = case duplicates rules of
      [] -> Right root {grammarRules = filter (kept rules) rules}
      ds -> Left ds
    kept rules =
      let reached = reachable rules (map ruleName (grammarRules root) ++ directiveRules root)
       in \r -> locFile (ruleLoc r) == 0 || S.member (ruleName r) reached

SOURCE
sed -n '/^resolveImports ::/,/^-- | The errors of a library on its own/p' "$source_file" |
  sed '$d' | diff -u "$work/expected" -

cat > "$work/expected" <<'SOURCE'
reachable :: [Rule] -> [Text] -> S.Set Text
reachable rules = go S.empty
  where
    byName = M.fromList [(ruleName r, r) | r <- rules]
    go seen = \case
      [] -> seen
      n : ns
        | S.member n seen -> go seen ns
        | otherwise -> go (S.insert n seen) (maybe [] ruleRefs (M.lookup n byName) ++ ns)
SOURCE
sed -n '/^reachable ::/,/^$/p' "$source_file" | sed '$d' | diff -u "$work/expected" -

cat > "$work/expected" <<'SOURCE'
duplicates :: [Rule] -> [Diagnostic]
duplicates rules =
  [ Diagnostic (ruleLoc r) ("duplicate definition of " <> ruleName r)
  | (seen, r) <- zip (scanl (flip (S.insert . ruleName)) S.empty rules) rules
  , S.member (ruleName r) seen
  ]

-- A diagnostic in the file of the given number.
inFile :: Int -> Diagnostic -> Diagnostic
inFile i (Diagnostic l m) = Diagnostic (l {locFile = i}) m
SOURCE
sed -n '/^duplicates ::/,/^inFile i /p' "$source_file" | diff -u "$work/expected" -

# The model moves only ruleLoc to the file of the library (the probe compares
# ruleLoc); relocateRule also moves every other location of the rule. Pin it.
sed -n '/^relocateRule ::/,$p' "$source_file" > "$work/relocate"
[ "$(git hash-object --stdin < "$work/relocate")" = ffb944dbcc85fede54261af7ce913d1752d57950 ]

# The probe takes directiveRules and ruleRefs from the source itself.
{
  cat <<'SOURCE'
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where
import Control.Monad (forM)
import Data.List (intercalate)
import Data.Maybe (isJust, maybeToList)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Assemble (Top (..), assemble)
import Peg.Grammar.Import (libraryErrors, resolveImports)
import Peg.Grammar.Parser (parseGrammar, parseTops)
import System.Environment (getArgs)
import System.Exit (die)
SOURCE
  sed -n '/^directiveRules ::/,/^$/p' "$source_file"
  sed -n '/^ruleRefs ::/,/^$/p' "$source_file"
  cat verification/ImportResolutionProbe.hs
} > "$work/Probe.hs"

"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -Wall -Werror \
  -package=peg-grammar "$work/Probe.hs" "$work/cases.lean" "$work/haskell-output"

cat verification/ImportResolutionProbe.lean "$work/cases.lean" > "$work/ImportResolutionRun.lean"
(cd verification &&
  LEAN_PATH="$work" lean -o "$work/ImportResolution.olean" ImportResolution.lean > /dev/null &&
  LEAN_PATH="$work" lean --run "$work/ImportResolutionRun.lean" > "$work/lean-output")

diff -u "$work/haskell-output" "$work/lean-output"
printf 'Compared %s resolveImports cases with the Lean model.\n' \
  "$(grep -c -E ' (ok|error)$' "$work/lean-output")"
