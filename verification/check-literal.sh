#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

[ -f "$LEAN_PATH/Literal.olean" ] || {
  echo 'Literal.olean is missing' >&2
  exit 1
}

cat > "$scratch/expected" <<'SOURCE'
hsString :: Text -> Text
hsString = T.pack . show . T.unpack
SOURCE
sed -n '/^hsString ::/,/^hsString =/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/expected" -

cat > "$scratch/expected" <<'SOURCE'
  ELit t orig -> pure ("PegRt.lit " <> hsString t <> " " <> hsString orig)
SOURCE
sed -n '/^  ELit t orig ->/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/expected" -

cat > "$scratch/LiteralProbe.lean" <<'SOURCE'
import Literal

def main : IO Unit := do
  let numbers := List.range 128 ++ [128, 255, 256, 65535, 65536, 1114111]
  for n in numbers do
    let c := Char.ofNat n
    IO.println s!"{n}\t{Peg.Verification.encodeLiteral (String.singleton c)}"
  for n in numbers do
    for m in numbers do
      let chars := String.ofList [Char.ofNat n, Char.ofNat m]
      IO.println s!"{n},{m}\t{Peg.Verification.encodeLiteral chars}"
SOURCE
(cd verification && lean --run "$scratch/LiteralProbe.lean") > "$scratch/lean-literal.txt"

cat > "$scratch/LiteralProbe.hs" <<'SOURCE'
import Data.Char (chr, ord)

main :: IO ()
main = do
  let chars = map chr ([0 .. 127] ++ [128, 255, 256, 65535, 65536, 1114111])
  mapM_ (\c -> putStrLn (show (ord c) ++ "\t" ++ show [c])) chars
  mapM_ (\c -> mapM_ (\d -> putStrLn
    (show (ord c) ++ "," ++ show (ord d) ++ "\t" ++ show [c, d])) chars) chars
SOURCE
runghc-9.10.3 "$scratch/LiteralProbe.hs" > "$scratch/haskell-literal.txt"
diff -u "$scratch/haskell-literal.txt" "$scratch/lean-literal.txt"
printf 'Compared 134 single-character and 17956 two-character literals with GHC Show.\n'

grep -Fxq 'showT = T.pack . show' packages/peg-codegen/src/Peg/Codegen.hs
cat > "$scratch/LiteralLexer.hs" <<'SOURCE'
import Control.Monad (forM_)
import Data.Char (chr)
import GHC (getSessionDynFlags, runGhc)
import GHC.Data.FastString (mkFastString, unpackFS)
import GHC.Data.StringBuffer (stringToStringBuffer)
import GHC.Driver.Config.Parser (initParserOpts)
import GHC.Parser.Lexer
import GHC.Types.SrcLoc (mkRealSrcLoc, unLoc)
import System.Environment (getArgs)

main :: IO ()
main = do
  [libdir, fixture] <- getArgs
  opts <- runGhc (Just libdir) (initParserOpts <$> getSessionDynFlags)
  rows <- lines <$> readFile fixture
  let loc = mkRealSrcLoc (mkFastString "LiteralProbe") 1 1
  forM_ rows $ \row -> case break (== '\t') row of
    (numbers, '\t' : literal) -> do
      let expected = map chr (read ("[" ++ numbers ++ "]"))
      case lexTokenStream opts (stringToStringBuffer literal) loc of
        POk _ tokens -> case map unLoc tokens of
          [ITstring _ value] | unpackFS value == expected -> pure ()
          actual -> fail ("unexpected literal tokens at " ++ numbers ++ ": " ++ show actual)
        PFailed _ -> fail ("lexer rejected " ++ numbers)
    _ -> fail "malformed literal fixture"
  putStrLn ("Checked " ++ show (length rows) ++ " GHC string tokens and decoded values.")
  forM_ ([0..0xd7ff] ++ [0xe000..0x10ffff]) $ \n -> do
    let c = chr n
        pair = "(" ++ show c ++ ", " ++ show c ++ ")"
    case lexTokenStream opts (stringToStringBuffer pair) loc of
      POk _ tokens -> case map unLoc tokens of
        [IToparen, ITchar _ lo, ITcomma, ITchar _ hi, ITcparen]
          | lo == c && hi == c -> pure ()
        actual -> fail ("unexpected range tokens at " ++ show n ++ ": " ++ show actual)
      PFailed _ -> fail ("lexer rejected range at " ++ show n)
  putStrLn "Checked all 1112064 Unicode scalars in both range endpoint positions."
SOURCE
runghc-9.10.3 -package=ghc "$scratch/LiteralLexer.hs" "$(ghc-9.10.3 --print-libdir)" "$scratch/lean-literal.txt"

# Compare the per-character spelling exhaustively. Buffered batches avoid
# performing a separate write for each Unicode scalar.
cat > "$scratch/ScalarSpellings.lean" <<'SOURCE'
import Literal

def main : IO Unit := do
  let out ← IO.getStdout
  for page in [:4352] do
    let mut rows := ""
    for offset in [:256] do
      let n := page * 256 + offset
      if n < 0xd800 || n > 0xdfff then
        rows := rows ++ Peg.Verification.encodeLiteral (String.singleton (Char.ofNat n)) ++ "\n"
    out.putStr rows
SOURCE
(cd verification && lean --run "$scratch/ScalarSpellings.lean") > "$scratch/scalar-spellings.txt"
cat > "$scratch/ScalarSpellings.hs" <<'SOURCE'
import Control.Monad (unless)
import Data.Char (chr)

main :: IO ()
main = do
  actual <- lines <$> getContents
  let scalars = [0..0xd7ff] ++ [0xe000..0x10ffff]
      spelling n = show [chr n]
  unless (map spelling scalars == actual) $
    fail "GHC and Lean differ on Unicode scalar spelling"
SOURCE
runghc-9.10.3 "$scratch/ScalarSpellings.hs" < "$scratch/scalar-spellings.txt"
printf 'Compared all 1112064 Unicode scalar spellings with GHC Show.\n'
