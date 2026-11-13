module Main (main) where

import Data.List (tails)
import Data.Char (isAsciiLower, isSpace)
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

main :: IO ()
main = do
  [path] <- getArgs
  source <- lines <$> readFile path
  let indented [] = True
      indented (c : _) = isSpace c
      definitions = [unlines (takeWhile indented rest) | "reservedWords =" : rest <- tails source]
  case definitions of
    [expression] | Just names <- readMaybe expression :: Maybe [String]
                 , all (\name -> not (null name) && all (\c -> isAsciiLower c || c == '_') name) names ->
      putStrLn ("def PegHs.grammarReservedWords : List String := " ++ show names)
    _ -> die "unsupported reservedWords definition"
