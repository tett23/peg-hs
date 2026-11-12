module Main (main) where

import Control.Monad (unless)
import qualified Data.Text as T
import qualified Peg.Runtime.Internal as R
import System.Exit (die)

data Store s = Store

check :: String -> String -> String -> Int -> Int -> IO ()
check before body after start end = do
  let parser = do
        R.lit before before
        i <- R.getOffset
        text <- R.capture (R.lit body body)
        j <- R.getOffset
        R.lit after after
        pure (i, text, j)
      input = T.pack (before ++ body ++ after)
      actual = fst (R.runParser R.defaultConfig (pure Store) parser input)
  unless (actual == Right (start, T.pack body, end)) $
    die ("invariant1: unexpected UTF-8 capture " ++ show actual)

main :: IO ()
main = do
  check "" "" "" 0 0
  check "a" "é中🙂" "z" 1 10
  check "🙂" "" "é" 4 4
  check "中é" "x" "" 5 6
