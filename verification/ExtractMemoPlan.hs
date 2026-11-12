{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (forM_)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Grammar (grammarRules, ruleName)
import Peg.Grammar.Check (Memoisation (..), check, ruleMemoisation)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  [path] <- getArgs
  source <- TIO.readFile path
  grammar <- either (die . show) pure (parseGrammar source >>= expandTemplates)
  analysis <- either (die . show) pure (check grammar)
  forM_ (grammarRules grammar) $ \rule -> do
    let kind = case ruleMemoisation grammar analysis rule of
          Memoised -> "memo"
          MemoisedWithArguments -> "memoArg"
          MemoisedLeftRecursive -> "memoLR"
          NotMemoised -> "nomemo"
    putStrLn (T.unpack (ruleName rule) ++ "\t" ++ kind)
