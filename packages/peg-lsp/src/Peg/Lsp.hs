-- | The language server of the @.peg@ notation over standard input and
-- output (ADR 0035). The handling of messages is in "Peg.Lsp.Server"; this
-- module only reads and writes the framed messages ("Peg.Lsp.Rpc").
--
-- @peg-hs lsp@ is this function applied to the standard handles:
--
-- @
-- import Peg.Lsp (runServer)
-- import System.Exit (ExitCode (..), exitWith)
-- import System.IO (stdin, stdout)
--
-- main :: IO ()
-- main = do
--   code <- runServer stdin stdout
--   exitWith (if code == 0 then ExitSuccess else ExitFailure code)
-- @
module Peg.Lsp
  ( runServer
  ) where

import qualified Data.ByteString as BS
import Peg.Lsp.Rpc (decodeFrames, encodeMessage)
import Peg.Lsp.Server
import System.IO

-- | Serve on an input and an output handle until the client sends @exit@
-- or closes the input, and return the exit status: 0 after a @shutdown@
-- request and 1 otherwise. Both handles are switched to binary mode; the
-- messages are UTF-8.
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
