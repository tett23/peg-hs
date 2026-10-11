-- | Positions in the input: byte offsets with lines and columns (ADR 0008,
-- ADR 0014).
module Peg.Runtime.Position
  ( Pos (..)
  , LineIndex
  , lineIndex
  , lineOf
  , posIn
  ) where

import Data.Array.Unboxed (UArray, bounds, listArray, (!))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Unsafe as TU

-- | A position in the input.
data Pos = Pos
  { posOffset :: !Int
  -- ^ Byte offset into the UTF-8 encoded input, starting at 0.
  , posLine :: !Int
  -- ^ Line number, starting at 1. Only LF starts a new line.
  , posColumn :: !Int
  -- ^ Column, starting at 1. Each Unicode code point, including a tab,
  -- counts as one column.
  }
  deriving (Eq, Ord, Show)

-- | The byte offsets where lines start.
type LineIndex = UArray Int Int

lineIndex :: Text -> LineIndex
lineIndex t = listArray (0, length starts - 1) starts
  where
    n = TU.lengthWord8 t
    starts = 0 : go 0
    go i
      | i >= n = []
      | otherwise =
          let TU.Iter c d = TU.iter t i
           in if c == '\n' then (i + d) : go (i + d) else go (i + d)

-- Index of the last line start that is <= the offset.
lineOf :: LineIndex -> Int -> Int
lineOf arr off = go lo hi
  where
    (lo, hi) = bounds arr
    go a b
      | a >= b = a
      | otherwise =
          let m = (a + b + 1) `div` 2
           in if arr ! m <= off then go m b else go a (m - 1)

-- | The position of a byte offset.
posIn :: Text -> LineIndex -> Int -> Pos
posIn input index off = Pos off (l + 1) (T.length (TU.takeWord8 (off - start) (TU.dropWord8 start input)) + 1)
  where
    l = lineOf index off
    start = index ! l
