#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"
[ -f "$LEAN_PATH/Pragmas.olean" ] || {
  echo 'Pragmas.olean is missing' >&2
  exit 1
}

cat > "$scratch/expected" <<'SOURCE'
    [] ->
      let unmarked = render opts g analysis ""
          marker = freshRestoreMarker (S.fromList (filter (T.isPrefixOf "{-# PEG'RESTORE_") (T.lines unmarked)))
       in Right (finalize opts marker (render opts g analysis marker))
SOURCE
sed -n '/^    \[\] ->$/,/^       in Right (finalize opts marker/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/expected" -

cat > "$scratch/expected" <<'SOURCE'
freshRestoreMarker :: Set Text -> Text
freshRestoreMarker occupied = choose 0
  where
    choose :: Int -> Text
    choose n =
      let marker = "{-# PEG'RESTORE_" <> T.replicate n "x" <> " #-}"
       in if S.member marker occupied then choose (n + 1) else marker
SOURCE
sed -n '/^freshRestoreMarker ::/,/^       in if S.member marker/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/expected" -

cat > "$scratch/expected" <<'SOURCE'
fragment :: (Int -> FilePath) -> Text -> Located Text -> Text
fragment sources marker (Located (Loc f l c) t) =
  T.concat
    [ "\n{-# LINE "
    , showT l
    , " "
    , T.pack (show (sources f))
    , " #-}\n {-# COLUMN "
    , showT c
    , " #-}"
    , t
    , "\n"
    , marker
    , "\n    "
    ]
SOURCE
sed -n '/^fragment ::/,/^    ]/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/expected" -

cat > "$scratch/expected" <<'SOURCE'
finalize opts marker t = T.unlines (zipWith fix [1 :: Int ..] (T.lines t))
  where
    fix n line
      | line == marker = "{-# LINE " <> showT (n + 1) <> " " <> T.pack (show (optOutputName opts)) <> " #-}"
      | otherwise = line
SOURCE
sed -n '/^finalize opts marker t =/,/^      | otherwise =/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/expected" -

cat > "$scratch/expected" <<'SOURCE'
showT :: Show a => a -> Text
showT = T.pack . show
SOURCE
sed -n '/^showT ::/,/^showT =/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/expected" -

cat > "$scratch/PragmasProbe.lean" <<'SOURCE'
import Pragmas

def main : IO Unit := do
  let path := "a\"\\\n\tZ"
  let marker := Peg.Verification.exampleMarker
  for input in ["", "\n", "\n\n", "x", "x\n", "x\r\n", marker,
      marker ++ "\n\n" ++ marker ++ "\n", "x\n" ++ marker ++ "\ny"] do
    IO.println ((Peg.Verification.finalizeText marker path input).toList.map Char.toNat)
  for n in [0, 1, 9, 10, 99, 100, 65535] do
    IO.println (Peg.Verification.renderLine n path)
    IO.println (Peg.Verification.renderColumn n)
    IO.println (Peg.Verification.renderFragment Peg.Verification.exampleMarker n n path "body")
    IO.println (Peg.Verification.finalizeLine Peg.Verification.exampleMarker n path Peg.Verification.exampleMarker)
    IO.println (Peg.Verification.finalizeLine Peg.Verification.exampleMarker n path "ordinary line")
SOURCE
(cd verification && lean --run "$scratch/PragmasProbe.lean") > "$scratch/lean-pragmas.txt"

cat > "$scratch/PragmasProbe.hs" <<'SOURCE'
{-# LANGUAGE OverloadedStrings #-}
import qualified Data.Text as T
import Data.List (intercalate)
main :: IO ()
main = do
  let path :: String
      path = "a\"\\\n\tZ"
  let marker = "{-# PEG'RESTORE_ #-}"
      finalize t = T.unlines (zipWith fix [1 :: Int ..] (T.lines t))
      fix n line | line == marker = T.pack ("{-# LINE " ++ show (n + 1) ++ " " ++ show path ++ " #-}")
                 | otherwise = line
  mapM_ (\t -> putStrLn ("[" ++ intercalate ", " (map (show . fromEnum) (T.unpack (finalize t))) ++ "]"))
    ["", "\n", "\n\n", "x", "x\n", "x\r\n", marker, marker <> "\n\n" <> marker <> "\n", "x\n" <> marker <> "\ny"]
  mapM_ (\n -> do
    let line = "{-# LINE " ++ show n ++ " " ++ show path ++ " #-}"
        col = "{-# COLUMN " ++ show n ++ " #-}"
    putStrLn line
    putStrLn col
    putStrLn ("\n" ++ line ++ "\n " ++ col ++ "body\n{-# PEG'RESTORE_ #-}\n    ")
    putStrLn ("{-# LINE " ++ show (n + 1) ++ " " ++ show path ++ " #-}")
    putStrLn "ordinary line")
    [0, 1, 9, 10, 99, 100, 65535 :: Int]
SOURCE
runghc-9.10.3 "$scratch/PragmasProbe.hs" > "$scratch/haskell-pragmas.txt"
diff -u "$scratch/haskell-pragmas.txt" "$scratch/lean-pragmas.txt"
printf 'Compared 7 line, column, fragment, and restore frames with GHC Show.\n'

# Compare the action at line 3, column 11 with the text written by the CLI.
# Both paths exercise quoting in real LINE pragmas.
cabal=${CABAL:-cabal}
peg=$("$cabal" list-bin exe:peg-hs)
input='Frame"Source.hpeg'
output='Frame"Output.hs'
printf '%s\n' '%module FrameProbe' 'S :: ()' "S <- 'a' { id () }" > "$scratch/$input"
(cd "$scratch" && "$peg" gen "$input" -o "$output")
cat > "$scratch/CheckFrame.lean" <<'SOURCE'
import Pragmas
open Peg.Verification

def main (args : List String) : IO Unit := do
  let [file, src, out] := args | throw (IO.userError "expected file and two pragma paths")
  let lines := (← IO.FS.readFile file).splitOn "\n" |>.toArray
  let mut matchesFound := 0
  for i in [:lines.size] do
    if lines[i]? == some (renderLine 3 src) then
      unless lines[i+1]? == some (" " ++ renderColumn 11 ++ " id () ") &&
          lines[i+2]? == some (finalizeLine exampleMarker (i+3) out exampleMarker) do
        throw (IO.userError "incorrect source or restore pragma around the generated action")
      matchesFound := matchesFound + 1
  unless matchesFound == 1 do throw (IO.userError "expected one generated action")
SOURCE
(cd verification && lean --run "$scratch/CheckFrame.lean" "$scratch/$output" "$input" "$output")
"$cabal" exec -- ghc-9.10.3 -fno-code -fforce-recomp -package peg-runtime \
  -outputdir "$scratch" "$scratch/$output"
