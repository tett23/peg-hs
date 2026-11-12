module Main (main) where

import Control.Monad (unless)
import Data.Char (digitToInt, isHexDigit, ord)
import Data.Function (on)
import Data.List (groupBy, intercalate, isInfixOf, stripPrefix)
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

main :: IO ()
main = do
  [file] <- getArgs
  source <- lines <$> readFile file
  let plain = ["    go l acc = \\case",
               "      [] -> Left (Diagnostic l \"unterminated literal\")",
               "      '\"' : rest -> Right (T.pack (reverse acc), rest)",
               "      '\\\\' : rest -> escape l (next l '\\\\') acc rest",
               "      c : rest -> go (next l c) (c : acc) rest"]
  unless (plain `isInfixOf` source) (die "unsupported literal decoder branch")
  let branch = [ "    escape back l acc = \\case"
               , "      [] -> Left (Diagnostic l \"unterminated literal\")"
               , "      'u' : rest -> unicode back (next l 'u') acc rest"
               , "      c : rest -> case lookup c simple of"
               , "        Just d -> go (next l c) (d : acc) rest"
               , "        Nothing -> Left (Diagnostic l (\"unknown escape \\\\\" <> T.singleton c))" ]
  unless (branch `isInfixOf` source) (die "unsupported escape branch")
  case [entries | line <- source, Just raw <- [stripPrefix "    simple = " line],
                  Just entries <- [readMaybe raw :: Maybe [(Char, Char)]]] of
    [entries] -> do
      putStrLn "import AssembleValidationHelpers"
      putStrLn "namespace PegHs.TranslatedEscapes"
      let digits = [(ord c, ord c - digitToInt c) | c <- [minBound .. maxBound], isHexDigit c]
          groups = groupBy ((==) `on` snd) digits
      putStrLn "def hexDigit (c : Char) : Option Nat :="
      mapM_ emitRange groups
      putStrLn "  none"
      putStrLn "def table : List (Char × Char) :="
      putStrLn ("  [" ++ intercalate ", " (map pair entries) ++ "]")
      putStrLn "def escape (go unicode : List Char → List Char → Except String α)"
      putStrLn "    (acc : List Char) : List Char → Except String α"
      putStrLn "  | [] => .error \"unterminated literal\""
      putStrLn "  | 'u' :: rest => unicode acc rest"
      putStrLn "  | c :: rest => match table.lookup c with"
      putStrLn "    | some d => go (d :: acc) rest"
      putStrLn "    | none => .error (\"unknown escape \\\\\" ++ String.singleton c)"
      putStrLn "def plain (go escaped : List Char → List Char → Except String (List Char × List Char))"
      putStrLn "    (acc : List Char) : List Char → Except String (List Char × List Char)"
      putStrLn "  | [] => .error \"unterminated literal\""
      putStrLn "  | '\"' :: rest => .ok (acc.reverse, rest)"
      putStrLn "  | '\\\\' :: rest => escaped acc rest"
      putStrLn "  | c :: rest => go (c :: acc) rest"
      putStrLn "end PegHs.TranslatedEscapes"
    _ -> die "unsupported simple escape table"
  where
    emitRange [] = die "empty hexadecimal range"
    emitRange xs@((lo, offset):_) = do
      let hi = fst (last xs)
      unless (map fst xs == [lo .. hi]) (die "non-contiguous hexadecimal range")
      putStrLn ("  if " ++ show lo ++ " ≤ c.toNat && c.toNat ≤ " ++ show hi
        ++ " then some (c.toNat - " ++ show offset ++ ") else")
    pair (a,b) = "(Char.ofNat " ++ show (ord a) ++ ", Char.ofNat " ++ show (ord b) ++ ")"
