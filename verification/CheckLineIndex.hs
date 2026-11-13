module Main (main) where

import Control.Monad (forM_, replicateM, unless)
import Data.Array.Unboxed (elems)
import Data.List (inits)
import qualified Data.ByteString as BS
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Peg.Runtime.Position (Pos (..), lineIndex, posIn)
import System.Exit (die)

check :: String -> IO ()
check chars = do
  let input = T.drop 1 (T.pack ('中' : chars))
      index = lineIndex input
      prefixes = inits chars
      bytes = BS.length . encodeUtf8 . T.pack
      starts = 0 : [bytes p | p <- prefixes, take 1 (reverse p) == "\n"]
  unless (elems index == starts) $
    die ("invariant2: incorrect line starts for " ++ show chars)
  forM_ prefixes $ \p -> do
    let off = bytes p
        line = 1 + length (filter (== '\n') p)
        column = 1 + length (takeWhile (/= '\n') (reverse p))
        actual = posIn input index off
    unless (actual == Pos off line column) $
      die ("invariant2: unexpected position " ++ show (chars, p, actual))

main :: IO ()
main = mapM_ check (concatMap (`replicateM` "a\t\r\né中🙂") [0 .. 4])
