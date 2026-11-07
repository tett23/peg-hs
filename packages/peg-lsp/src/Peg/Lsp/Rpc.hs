-- | The base protocol of the language server protocol: messages framed by a
-- @Content-Length@ header (ADR 0035).
--
-- 'decodeFrames' splits the bytes read so far into message bodies, and
-- 'encodeMessage' frames a message to send. "Peg.Lsp" runs them around
-- 'Peg.Lsp.Server.handleFrame'.
--
-- A message has limits on the length of its header and of its body
-- (ADR 0077), so that the bytes kept for a message that has not arrived
-- in full are at most 'maxHeaderLength' and 'maxContentLength' together.
module Peg.Lsp.Rpc
  ( encodeMessage
  , decodeFrames
  , FrameError (..)
  , renderFrameError
  , maxHeaderLength
  , maxContentLength
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import Data.Char (isSpace, toLower)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Peg.Lsp.Json
import Text.Read (readMaybe)

-- | A message with its header.
encodeMessage :: Value -> BS.ByteString
encodeMessage v =
  let body = TE.encodeUtf8 (renderJson v)
   in BC.pack ("Content-Length: " <> show (BS.length body) <> "\r\n\r\n") <> body

-- | The longest header of a message, with the empty line that ends it:
-- 65536 bytes (64 KiB). A header has a @Content-Length@ and, at most, a
-- @Content-Type@, some tens of bytes; the limit leaves room for any client,
-- and bounds the bytes searched for the end of a header.
maxHeaderLength :: Int
maxHeaderLength = 65536

-- | The longest body of a message, its @Content-Length@: 67108864 bytes
-- (64 MiB). The largest messages carry a whole grammar, which is far
-- smaller; the limit bounds the memory that a client that does not send
-- the body it announced can make the server keep.
maxContentLength :: Int
maxContentLength = 67108864

-- | Why the bytes read so far cannot start a message within the limits.
-- After it the start of the next message is unknown, so the server stops.
data FrameError
  = -- | No end of the header within 'maxHeaderLength' bytes.
    HeaderTooLong
  | -- | A @Content-Length@ over 'maxContentLength'.
    BodyTooLong Integer
  deriving (Eq, Show)

-- | The reason of an error, in a line.
renderFrameError :: FrameError -> Text
renderFrameError = \case
  HeaderTooLong -> "a message header longer than " <> T.pack (show maxHeaderLength) <> " bytes"
  BodyTooLong n -> "a message body of " <> T.pack (show n) <> " bytes, longer than " <> T.pack (show maxContentLength) <> " bytes"

-- | The complete messages at the start of the bytes read so far, and the
-- bytes left over, or the error that ends the messages. A message whose
-- header has no length, or whose body is not UTF-8, is an error and is
-- skipped. A header or a body over the limits is an error as soon as it
-- is known to be, before the rest of the message arrives; a header and a
-- body of the limits are read.
decodeFrames :: BS.ByteString -> ([Either Text Text], Either FrameError BS.ByteString)
decodeFrames buf =
  case BS.breakSubstring "\r\n\r\n" (BS.take maxHeaderLength buf) of
    (_, rest)
      | BS.null rest -> ([], if BS.length buf > maxHeaderLength then Left HeaderTooLong else Right buf)
    (header, _) ->
      let afterHeader = BS.drop (BS.length header + 4) buf
       in case contentLength header of
            Nothing -> more (Left "a message header without Content-Length") afterHeader
            Just n
              | n > fromIntegral maxContentLength -> ([], Left (BodyTooLong n))
              | BS.length afterHeader < fromInteger n -> ([], Right buf)
              | otherwise ->
                  let (body, after) = BS.splitAt (fromInteger n) afterHeader
                   in more (either (const (Left "a message body that is not UTF-8")) Right (TE.decodeUtf8' body)) after
  where
    more m after = let (ms, left) = decodeFrames after in (m : ms, left)

-- The length of the body, as an Integer, so that a number too large for an
-- Int is over the limit rather than wrapped around.
contentLength :: BS.ByteString -> Maybe Integer
contentLength header =
  case [v | l <- BC.lines (BC.filter (/= '\r') header), let (k, v) = BC.break (== ':') l, map toLower (BC.unpack k) == "content-length"] of
    v : _ -> readMaybe (dropWhile isSpace (drop 1 (BC.unpack v))) >>= \n -> if n >= 0 then Just n else Nothing
    [] -> Nothing
