-- | A hand-written JSON serialiser, used by the round-trip test.
module Conformance.Json.Encode
  ( encode
  ) where

import Conformance.Json.Parser (Value (..))
import Data.Char (ord)
import Data.Text (Text)
import qualified Data.Text as T
import Numeric (showHex)

encode :: Value -> Text
encode v = case v of
  Null -> T.pack "null"
  Bool True -> T.pack "true"
  Bool False -> T.pack "false"
  Number n -> n
  String s -> string s
  Array vs -> T.concat [T.pack "[", T.intercalate (T.pack ",") (map encode vs), T.pack "]"]
  Object ms ->
    T.concat
      [ T.pack "{"
      , T.intercalate (T.pack ",") [string k <> T.pack ":" <> encode x | (k, x) <- ms]
      , T.pack "}"
      ]

string :: Text -> Text
string s = T.concat [T.pack "\"", T.concatMap escape s, T.pack "\""]
  where
    escape c
      | c == '"' = T.pack "\\\""
      | c == '\\' = T.pack "\\\\"
      | ord c < 0x20 = T.pack ("\\u" <> pad (showHex (ord c) ""))
      | otherwise = T.singleton c
    pad h = replicate (4 - length h) '0' <> h
