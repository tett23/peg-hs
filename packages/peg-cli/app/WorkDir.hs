{-# LANGUAGE CPP #-}

-- | The working directory of @peg-hs parse@ (ADR 0077): a directory of its
-- own under the temporary directory, readable only by its owner, removed
-- whatever happens to the work in it.
--
-- The directory is made by one @mkdir@ with a random name. A name that is
-- taken, by a directory, a file or a link, makes the @mkdir@ fail, and
-- another name is tried, so that a path that someone else made beforehand
-- is never used. On POSIX the directory is made with the permission 0700;
-- on Windows the temporary directory is the user's own.
module WorkDir
  ( withWorkDir
  , withWorkDirIn
  , createWorkDir
  , workDirName
  , maxAttempts
  ) where

import Control.Exception (bracket, throwIO)
import Data.Bits (shiftR, xor)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import Numeric (showHex)
import System.Directory (getTemporaryDirectory, removePathForcibly)
import System.FilePath ((</>))
import System.IO.Error (catchIOError, isAlreadyExistsError)
import System.Process (getCurrentPid)
#if defined(mingw32_HOST_OS)
import qualified System.Directory as D
#else
import qualified System.Posix.Directory as P
#endif

-- | Run an action in a fresh working directory under the temporary
-- directory, and remove the directory after it, on a success, a failure or
-- an exception.
withWorkDir :: (FilePath -> IO a) -> IO a
withWorkDir act = do
  tmp <- getTemporaryDirectory
  withWorkDirIn workDirName tmp act

-- | 'withWorkDir' with the names of the attempts and the parent directory.
withWorkDirIn :: (Int -> IO String) -> FilePath -> (FilePath -> IO a) -> IO a
withWorkDirIn names parent = bracket (createWorkDir names parent) removePathForcibly

-- | Make a directory under a parent with the name of the first attempt
-- whose name is not taken, trying at most 'maxAttempts' names; the
-- attempts are numbered from 0. Another error than a taken name is thrown
-- at once.
createWorkDir :: (Int -> IO String) -> FilePath -> IO FilePath
createWorkDir names parent = go 0
  where
    go attempt
      | attempt >= maxAttempts =
          ioError (userError ("cannot make a working directory under " <> parent <> ": " <> show maxAttempts <> " names were taken"))
      | otherwise = do
          path <- (parent </>) <$> names attempt
          made <- (makePrivateDirectory path >> pure True) `catchIOError` \e -> if isAlreadyExistsError e then pure False else throwIO e
          if made then pure path else go (attempt + 1)

-- | The number of names 'createWorkDir' tries: 100.
maxAttempts :: Int
maxAttempts = 100

-- | A name for an attempt, from the time, the process and the attempt. The
-- name is hard to guess; that it is not taken is checked by the @mkdir@.
workDirName :: Int -> IO String
workDirName attempt = do
  time <- getMonotonicTimeNSec
  pid <- getCurrentPid
  let h = mix (mix (time `xor` mix (fromIntegral pid)) `xor` fromIntegral attempt)
  pure ("peg-hs-parse-" <> hex16 h)

-- The finalizer of SplitMix64: each bit of the input changes about half
-- of the bits of the output.
mix :: Word64 -> Word64
mix z0 =
  let z1 = (z0 `xor` (z0 `shiftR` 30)) * 0xbf58476d1ce4e5b9
      z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94d049bb133111eb
   in z2 `xor` (z2 `shiftR` 31)

hex16 :: Word64 -> String
hex16 w = let s = showHex w "" in replicate (16 - length s) '0' <> s

-- One mkdir, which fails if the path exists in any form, even as a
-- dangling link.
makePrivateDirectory :: FilePath -> IO ()
#if defined(mingw32_HOST_OS)
makePrivateDirectory = D.createDirectory
#else
makePrivateDirectory path = P.createDirectory path 0o700
#endif
