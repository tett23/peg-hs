module Main (main) where

import Control.Monad (unless)
import Data.Char (ord)
import Data.List (intercalate, isInfixOf, stripPrefix)
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

main :: IO ()
main = do
  [file] <- getArgs
  source <- lines <$> readFile file
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
      putStrLn "def table : List (Char × Char) :="
      putStrLn ("  [" ++ intercalate ", " (map pair entries) ++ "]")
      putStrLn "def escape (go unicode : List Char → List Char → Except String α)"
      putStrLn "    (acc : List Char) : List Char → Except String α"
      putStrLn "  | [] => .error \"unterminated literal\""
      putStrLn "  | 'u' :: rest => unicode acc rest"
      putStrLn "  | c :: rest => match table.lookup c with"
      putStrLn "    | some d => go (d :: acc) rest"
      putStrLn "    | none => .error (\"unknown escape \\\\\" ++ String.singleton c)"
      putStrLn "end PegHs.TranslatedEscapes"
    _ -> die "unsupported simple escape table"
  where
    pair (a,b) = "(Char.ofNat " ++ show (ord a) ++ ", Char.ofNat " ++ show (ord b) ++ ")"
