-- | Running a process and taking its output as bytes, whatever the locale
-- (ADR 0045): the output of a parser or of GHC can contain any text, which
-- the encoding of the locale (ASCII in the C locale) cannot decode.
module ProcessBytes (readProcessBytes) where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Exception (evaluate)
import qualified Data.ByteString as BS
import System.Exit (ExitCode)
import System.IO (hClose, hSetBinaryMode)
import System.Process (CreateProcess (..), StdStream (..), createProcess, proc, waitForProcess)

-- | The exit code, the standard output and the standard error of a
-- process, with an empty standard input. The two outputs are read at once,
-- so that a process that fills one of them does not wait for the other.
readProcessBytes :: FilePath -> [String] -> IO (ExitCode, BS.ByteString, BS.ByteString)
readProcessBytes cmd args = do
  (Just i, Just o, Just e, ph) <- createProcess (proc cmd args) {std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe}
  hClose i
  mapM_ (`hSetBinaryMode` True) [o, e]
  errVar <- newEmptyMVar
  _ <- forkIO (BS.hGetContents e >>= evaluate >>= putMVar errVar)
  out <- BS.hGetContents o
  err <- takeMVar errVar
  code <- waitForProcess ph
  pure (code, out, err)
