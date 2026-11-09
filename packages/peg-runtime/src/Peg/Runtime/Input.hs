{-# LANGUAGE OverloadedStrings #-}

-- | The input text of UTF-8 bytes (ADR 0093).
module Peg.Runtime.Input
  ( decodeInput
  , Utf8Error (..)
  , renderUtf8Error
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (decodeUtf8', decodeUtf8Lenient, validateUtf8Chunk)
import Peg.Runtime.Position (Pos (..), lineIndex, posIn)

-- | Bytes that are not UTF-8.
newtype Utf8Error = Utf8Error
  { utf8ErrorPos :: Pos
  -- ^ The position of the first byte of the first ill-formed sequence.
  -- It is counted as the position of a t'Peg.Runtime.ParseError': the
  -- offset is in bytes after the byte order mark, if any, and the line and
  -- the column count the well-formed bytes before it.
  }
  deriving (Eq, Show)

-- | The input text of UTF-8 bytes, without a byte order mark at the start.
--
-- A byte order mark (@EF BB BF@) at the start is removed; one elsewhere is
-- kept as U+FEFF. Overlong encodings, surrogates, code points above
-- U+10FFFF and a sequence cut at the end are errors, and the error is the
-- position of the first ill-formed sequence. The text that is returned can
-- be given to the entry points of a generated module, and the positions of
-- their errors count the same bytes as those of t'Utf8Error'.
decodeInput :: ByteString -> Either Utf8Error Text
decodeInput bytes = case decodeUtf8' body of
  Right t -> Right t
  Left _ -> Left (Utf8Error (posIn prefix (lineIndex prefix) n))
  where
    body = fromMaybe bytes (BS.stripPrefix byteOrderMark bytes)
    n = fst (validateUtf8Chunk body)
    -- The well-formed bytes before the error: decoding them replaces nothing.
    prefix = decodeUtf8Lenient (BS.take n body)

byteOrderMark :: ByteString
byteOrderMark = BS.pack [0xEF, 0xBB, 0xBF]

-- | Render an error as @line:column: invalid UTF-8@, in the form of
-- 'Peg.Runtime.renderParseError'.
renderUtf8Error :: Utf8Error -> Text
renderUtf8Error (Utf8Error p) =
  T.concat [T.pack (show (posLine p)), ":", T.pack (show (posColumn p)), ": invalid UTF-8"]
