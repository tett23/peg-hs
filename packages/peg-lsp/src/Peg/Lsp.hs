-- | The language server of the @.peg@ notation over standard input and
-- output (ADR 0035). The handling of messages is in "Peg.Lsp.Server"; this
-- module only reads and writes the framed messages.
module Peg.Lsp
  ( runServer
  ) where

import qualified Data.ByteString as BS
import Peg.Lsp.Rpc (decodeFrames, encodeMessage)
import Peg.Lsp.Server
import System.IO

-- | Serve until the client sends @exit@ or closes the input; the exit
-- status is 0 after a @shutdown@ request and 1 otherwise.
runServer :: Handle -> Handle -> IO Int
runServer input output = do
  hSetBinaryMode input True
  hSetBinaryMode output True
  hSetBuffering output (BlockBuffering Nothing)
  loop initialState BS.empty
  where
    loop st buf = do
      chunk <- BS.hGetSome input 65536
      if BS.null chunk
        then pure 1
        else do
          let (frames, rest) = decodeFrames (buf <> chunk)
          handleAll st frames >>= \case
            Left code -> pure code
            Right st' -> loop st' rest
    handleAll st [] = pure (Right st)
    handleAll st (f : fs) = do
      let step = handleFrame st f
      mapM_ (BS.hPut output . encodeMessage) (stepOutput step)
      hFlush output
      case stepExit step of
        Just code -> pure (Left code)
        Nothing -> handleAll (stepState step) fs
