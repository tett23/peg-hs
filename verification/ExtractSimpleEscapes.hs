module Main (main) where

import Data.Char (ord)
import Data.List (stripPrefix)
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

main :: IO ()
main = do
  [file] <- getArgs
  source <- lines <$> readFile file
  case [entries | line <- source, Just raw <- [stripPrefix "    simple = " line],
                  Just entries <- [readMaybe raw :: Maybe [(Char, Char)]]] of
    [entries] -> do
      putStrLn "import AssembleValidationHelpers"
      putStrLn "namespace PegHs.TranslatedEscapes"
      putStrLn "def table : List (Char × Char) :="
      putStrLn ("  [" ++ joinPairs entries ++ "]")
      putStrLn "end PegHs.TranslatedEscapes"
    _ -> die "unsupported simple escape table"
  where
    pair (a,b) = "(Char.ofNat " ++ show (ord a) ++ ", Char.ofNat " ++ show (ord b) ++ ")"
    joinPairs [] = ""
    joinPairs [x] = pair x
    joinPairs (x:xs) = pair x ++ ", " ++ joinPairs xs
