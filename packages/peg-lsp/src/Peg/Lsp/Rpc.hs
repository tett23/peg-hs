-- | The base protocol of the language server protocol: messages framed by a
-- @Content-Length@ header (ADR 0035).
module Peg.Lsp.Rpc
  ( encodeMessage
  , decodeFrames
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import Data.Char (isSpace, toLower)
import Data.Text (Text)
import qualified Data.Text.Encoding as TE
import Peg.Lsp.Json
import Text.Read (readMaybe)

-- | A message with its header.
encodeMessage :: Value -> BS.ByteString
encodeMessage v =
  let body = TE.encodeUtf8 (renderJson v)
   in BC.pack ("Content-Length: " <> show (BS.length body) <> "\r\n\r\n") <> body

-- | The complete messages at the start of the bytes read so far, and the
-- bytes left over. A message whose header has no length, or whose body is
-- not UTF-8, is an error and is skipped.
decodeFrames :: BS.ByteString -> ([Either Text Text], BS.ByteString)
decodeFrames buf =
  case BS.breakSubstring "\r\n\r\n" buf of
    (_, rest) | BS.null rest -> ([], buf)
    (header, rest) ->
      let afterHeader = BS.drop 4 rest
       in case contentLength header of
            Nothing ->
              let (ms, left) = decodeFrames afterHeader
               in (Left "a message header without Content-Length" : ms, left)
            Just n
              | BS.length afterHeader < n -> ([], buf)
              | otherwise ->
                  let (body, after) = BS.splitAt n afterHeader
                      m = either (const (Left "a message body that is not UTF-8")) Right (TE.decodeUtf8' body)
                      (ms, left) = decodeFrames after
                   in (m : ms, left)

contentLength :: BS.ByteString -> Maybe Int
contentLength header =
  case [v | l <- BC.lines (BC.filter (/= '\r') header), let (k, v) = BC.break (== ':') l, map toLower (BC.unpack k) == "content-length"] of
    v : _ -> readMaybe (dropWhile isSpace (drop 1 (BC.unpack v))) >>= \n -> if n >= 0 then Just n else Nothing
    [] -> Nothing
