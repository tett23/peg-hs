-- | The WASI reactor of ADR 0078. The caller runs @_initialize@ and
-- @hs_init(0, 0)@ once, then calls 'analyze' and 'format' with the address
-- and the length in bytes of a request in UTF-8. Each returns the address
-- of a new block: the length in bytes of the response (4 bytes, little
-- endian, unsigned), then the response in UTF-8. The caller frees the
-- block with @free@. The request is copied before the function returns.
module Main (main) where

import Control.Exception (SomeException, displayException, evaluate, try)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BU
import Data.Bits (shiftR)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign (Ptr, Word8, castPtr, copyBytes, mallocBytes, plusPtr, pokeByteOff)
import Foreign.C.Types (CInt (..))
import Peg.Wasm (analyzeJson, errorJson, formatJson)

-- | A reactor has no main; GHC needs one for an executable.
main :: IO ()
main = pure ()

foreign export ccall analyze :: Ptr Word8 -> CInt -> IO (Ptr Word8)

foreign export ccall format :: Ptr Word8 -> CInt -> IO (Ptr Word8)

analyze :: Ptr Word8 -> CInt -> IO (Ptr Word8)
analyze = serve analyzeJson

format :: Ptr Word8 -> CInt -> IO (Ptr Word8)
format = serve formatJson

-- Copy the request, answer it, and catch every exception, so that the
-- wasm keeps running.
serve :: (Text -> Text) -> Ptr Word8 -> CInt -> IO (Ptr Word8)
serve f p n = do
  request <- BS.packCStringLen (castPtr p, fromIntegral n)
  result <- try (evaluate (forced (either (const (errorJson "the request is not UTF-8")) f (TE.decodeUtf8' request))))
  block $ case result of
    Right bytes -> bytes
    Left e -> TE.encodeUtf8 (errorJson ("internal error: " <> T.pack (displayException (e :: SomeException))))
  where
    -- A strict ByteString is the whole response, so evaluating it runs
    -- every part of the answer inside try.
    forced t = let bs = TE.encodeUtf8 t in BS.length bs `seq` bs

-- A new block with the length and the bytes.
block :: BS.ByteString -> IO (Ptr Word8)
block bs = do
  let n = BS.length bs
  q <- mallocBytes (4 + n)
  mapM_ (\i -> pokeByteOff q i (fromIntegral (n `shiftR` (8 * i)) :: Word8)) [0 .. 3]
  BU.unsafeUseAsCStringLen bs $ \(s, len) -> copyBytes (q `plusPtr` 4) (castPtr s) len
  pure q
