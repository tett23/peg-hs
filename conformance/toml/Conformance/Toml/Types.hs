-- | The values of the TOML grammar (ADR 0023): a document is a list of
-- lines, each a key and value, a table header, or nothing. Building the
-- nested document from the lines is "Conformance.Toml.Document".
module Conformance.Toml.Types
  ( Line (..)
  , Key
  , Val (..)
  , DateTime (..)
  , Time (..)
  , integerIn
  , floatOf
  , scalarValue
  , validDate
  ) where

import Data.Char (digitToInt)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Runtime (Span)

-- | A dotted key, each part decoded.
type Key = [Text]

data Line
  = LKeyVal Span Key Val
  | LTable Span Key
  | LArrayTable Span Key
  | LBlank
  deriving (Eq, Show)

data Val
  = VString Text
  | VInteger Integer
  | VFloat Double
  | VBool Bool
  | VDateTime DateTime
  | VArray [Val]
  | VInline [(Key, Val)]
  | -- | A value replaced by a recovery rule.
    VInvalid
  deriving (Eq, Show)

-- | A date, a time, and an offset in minutes. Which of them are present
-- tells the kind: all three is an offset date-time, date and time a local
-- date-time, and one alone a local date or a local time.
data DateTime = DateTime (Maybe (Int, Int, Int)) (Maybe Time) (Maybe Int)
  deriving (Eq, Show)

-- | Hours, minutes, seconds, and the digits of the fraction of a second.
data Time = Time Int Int Int Text
  deriving (Eq, Show)

-- | An integer in the given base, with underscores between digits.
integerIn :: Integer -> Text -> Integer
integerIn base = T.foldl' step 0
  where
    step n '_' = n
    step n c = n * base + toInteger (digitToInt c)

-- | The value of a float lexeme without its sign, underscores dropped. The
-- grammar guarantees digits on both sides of a decimal point, which
-- Haskell's 'read' requires.
floatOf :: Text -> Double
floatOf = read . T.unpack . T.filter (/= '_')

-- | Whether a code point written as an escape is a Unicode scalar value.
scalarValue :: Integer -> Bool
scalarValue n = n <= 0x10FFFF && not (0xD800 <= n && n <= 0xDFFF)

-- | Whether a date exists in the proleptic Gregorian calendar.
validDate :: Int -> Int -> Int -> Bool
validDate y m d = m >= 1 && m <= 12 && d >= 1 && d <= daysIn m
  where
    leap = (y `mod` 4 == 0 && y `mod` 100 /= 0) || y `mod` 400 == 0
    daysIn 2 = if leap then 29 else 28
    daysIn k
      | k `elem` [4, 6, 9, 11] = 30
      | otherwise = 31
