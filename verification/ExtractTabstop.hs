module Main (main) where

import Control.Monad (unless)
import Data.Char (digitToInt, isDigit, ord)
import Data.List (isInfixOf, tails)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  [file] <- getArgs
  source <- lines <$> readFile file
  let signature = "positiveTabstop :: Text -> Maybe Int"
  let clauses =
        [ [ "    single n = case [Located l a | (l, n', a) <- directives, n' == n] of"
          , "      x : _ -> Just x", "      [] -> Nothing" ]
        , [ "    tabstop = case single \"tabstop\" of"
          , "      Just (Located l a) -> Located l <$> positiveTabstop a", "      _ -> Nothing" ]
        , [ "        ++ [ Diagnostic l \"%tabstop expects a positive integer\""
          , "           | Just (Located l _) <- [single \"tabstop\"]", "           , Nothing <- [tabstop]", "           ]" ]
        ]
  unless (all (`isInfixOf` source) clauses) (die "unsupported tabstop selection or diagnostic")
  (divisor, multiplier) <- case [takeWhile (not . null) body | first : body <- tails source, first == signature] of
    [[ "positiveTabstop text = do", "  width <- foldM step 0 (T.unpack text)"
      , "  if width > 0 then Just width else Nothing", "  where", "    step acc c"
      , "      | isDigit c", "      , let digit = digitToInt c", guardLine
      , "      | otherwise = Nothing"]] ->
        case words guardLine of
          [",","acc","<=","(maxBound","-","digit)","`div`",d,"=","Just","(acc","*",m,"+","digit)"]
            | d `elem` bases, m `elem` bases -> pure (d, m)
          _ -> die "unsupported tabstop arithmetic"
    _ -> die "unsupported positiveTabstop definition"
  unless (all matchesDigit [minBound .. maxBound]) (die "unsupported GHC decimal character semantics")
  putStrLn "import BoundedDecimal"
  putStrLn "namespace PegHs.TranslatedTabstop"
  putStrLn ("def limit : Nat := " ++ show (maxBound :: Int))
  putStrLn "def step (acc : Nat) (c : Char) : Option Nat :="
  putStrLn "  let d := c.toNat - '0'.toNat"
  putStrLn ("  if c.isDigit && acc ≤ (limit - d) / " ++ divisor ++ " then some (acc * " ++ multiplier ++ " + d) else none")
  putStrLn "def positive (text : String) : Option Nat := do"
  putStrLn "  let width ← text.toList.foldlM step 0"
  putStrLn "  if width > 0 then some width else none"
  putStrLn "end PegHs.TranslatedTabstop"
  where
    bases = map show [2 .. 16 :: Int]
    matchesDigit c = isDigit c == ('0' <= c && c <= '9')
      && (not (isDigit c) || digitToInt c == ord c - ord '0')
