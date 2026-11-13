module Main (main) where

import Control.Monad (unless)
import Data.Char (chr, ord)
import qualified Data.Text as T
import qualified Data.Text.Unsafe as TU
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

-- Include nonzero byte offsets and Text values whose underlying array starts
-- before the slice. Surrogates cannot occur as scalars in UTF-8 text.
checkIterator :: IO ()
checkIterator = do
  let scalars = map chr ([0 .. 0xd7ff] ++ [0xe000 .. 0x10ffff])
      input = T.drop 1 (T.pack ('中' : scalars))
      walk offset [] = unless (offset == TU.lengthWord8 input) $
        die "invariant1: final iterator offset differs from UTF-8 length"
      walk offset (c : cs) =
        let TU.Iter actual width = TU.iter input offset
            expected
              | ord c <= 0x7f = 1
              | ord c <= 0x7ff = 2
              | ord c <= 0xffff = 3
              | otherwise = 4
         in if actual == c && width == expected
              then walk (offset + width) cs
              else die ("invariant1: unexpected UTF-8 iterator result at scalar " ++ show (ord c))
  walk 0 scalars

main :: IO ()
main = do
  checkIterator
  check "" "" "" 0 0
  check "a" "é中🙂" "z" 1 10
  check "🙂" "" "é" 4 4
  check "中é" "x" "" 5 6
