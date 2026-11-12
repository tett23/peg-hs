#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
extractor=${1:-verification/ExtractInnerUnicode.hs}
lean_file=${2:-verification/InnerUnicode.lean}
[ "$(ghc-9.10.3 --numeric-version)" = 9.10.3 ] || {
  echo 'GHC 9.10.3 is required for the Unicode snapshot.' >&2
  exit 1
}

expected_source=$(mktemp)
actual_ranges=$(mktemp)
committed_ranges=$(mktemp)
trap 'rm -f "$expected_source" "$actual_ranges" "$committed_ranges"' EXIT HUP INT TERM

# The extractor itself is part of the proof boundary. Changes require review.
cat > "$expected_source" <<'SOURCE'
import Data.Char (chr, isAlphaNum, isUpper)
import Numeric (showHex)

scalarPoints :: [Int]
scalarPoints = [0 .. 0xD7FF] ++ [0xE000 .. 0x10FFFF]

ranges :: (Char -> Bool) -> [(Int, Int)]
ranges predicate = reverse (go Nothing [] scalarPoints)
  where
    go current output [] = maybe output (: output) current
    go current output (point : rest)
      | predicate (chr point) = case current of
          Nothing -> go (Just (point, point)) output rest
          Just (first, lastPoint)
            | point == lastPoint + 1 -> go (Just (first, point)) output rest
            | otherwise -> go (Just (point, point)) ((first, lastPoint) : output) rest
      | otherwise = go Nothing (maybe output (: output) current) rest

hex :: Int -> String
hex value = "0x" ++ showHex value ""

emit :: String -> [(Int, Int)] -> IO ()
emit name spans = do
  putStrLn ("def " ++ name ++ " : List (Nat × Nat) := [")
  mapM_ (\(first, lastPoint) ->
    putStrLn ("  (" ++ hex first ++ ", " ++ hex lastPoint ++ "),")) spans
  putStrLn "]"

main :: IO ()
main = do
  emit "upperRanges" (ranges isUpper)
  emit "alphaNumRanges" (ranges isAlphaNum)
SOURCE
diff -u "$expected_source" "$extractor"

runghc-9.10.3 "$extractor" > "$actual_ranges"
[ "$(grep -c '^def upperRanges : List (Nat × Nat) := \[$' "$lean_file")" -eq 1 ]
[ "$(grep -c '^def alphaNumRanges : List (Nat × Nat) := \[$' "$lean_file")" -eq 1 ]
sed -n '/^def upperRanges : List (Nat × Nat) := \[$/,/^]$/p;/^def alphaNumRanges : List (Nat × Nat) := \[$/,/^]$/p' \
  "$lean_file" > "$committed_ranges"
diff -u "$actual_ranges" "$committed_ranges"

printf 'Checked 1112064 scalar values; upper ranges: 649; alphanumeric ranges: 748.\n'
