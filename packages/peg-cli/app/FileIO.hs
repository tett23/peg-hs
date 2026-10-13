{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

-- | Reading and writing the files of the commands as UTF-8, whatever the
-- locale, and short errors in place of the exceptions of GHC (ADR 0045).
module FileIO
  ( FileError (..)
  , Access (..)
  , Reason (..)
  , readUtf8
  , writeUtf8
  , renderFileError
  , reportFileError
  , decodeUtf8File
  , utf8ErrorOffset
  , setUtf8StdHandles
  ) where

import Control.Exception (IOException, try)
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text.Encoding as TE
import Data.Word (Word8)
import System.Directory (doesDirectoryExist, getCurrentDirectory)
import System.FilePath (isRelative, takeDirectory)
import System.IO (hPutStrLn, hSetEncoding, mkTextEncoding, stderr, stdout)
import System.IO.Error (isDoesNotExistError, isPermissionError)

data Access = Reading | Writing
  deriving (Eq, Show)

data Reason
  = NoSuchFile
  | IsDirectory
  | PermissionDenied
  | -- | The directory to write the file in does not exist.
    MissingDirectory FilePath
  | -- | The position of the first byte that is not UTF-8, from 1.
    NotUtf8 Int
  | OtherError String
  deriving (Eq, Show)

-- | A file that could not be read or written: the path as given, why, and
-- hints of what to do.
data FileError = FileError
  { feAccess :: Access
  , fePath :: FilePath
  , feReason :: Reason
  , feHints :: [String]
  }
  deriving (Eq, Show)

-- | The lines of the error, without a newline at the end.
renderFileError :: FileError -> [String]
renderFileError e =
  ("peg-hs: cannot " <> verb <> " " <> fePath e <> ": " <> reason) : map ("hint: " <>) (feHints e)
  where
    verb = case feAccess e of
      Reading -> "read"
      Writing -> "write"
    reason = case feReason e of
      NoSuchFile -> "no such file"
      IsDirectory -> "is a directory"
      PermissionDenied -> "permission denied"
      MissingDirectory d -> "directory " <> d <> " does not exist"
      NotUtf8 n -> "not UTF-8 (at byte " <> show n <> ")"
      OtherError s -> s

reportFileError :: FileError -> IO ()
reportFileError = mapM_ (hPutStrLn stderr) . renderFileError

-- | Read a file as UTF-8. @directoryHint@ is the hint when the path is a
-- directory, such as that the command takes a grammar file.
readUtf8 :: String -> FilePath -> IO (Either FileError Text)
readUtf8 directoryHint path = do
  isDir <- doesDirectoryExist path
  if isDir
    then pure (Left (FileError Reading path IsDirectory [directoryHint | not (null directoryHint)]))
    else
      try (BS.readFile path) >>= \case
        Right bytes -> pure (either (\n -> Left (FileError Reading path (NotUtf8 n) [utf8Hint])) Right (decodeUtf8File bytes))
        Left err -> Left <$> failure Reading path err
  where
    utf8Hint = "peg-hs reads grammars and inputs as UTF-8; convert the file to UTF-8"

-- | Write a file as UTF-8. The directory of the file must exist.
writeUtf8 :: FilePath -> Text -> IO (Either FileError ())
writeUtf8 path text = do
  let dir = takeDirectory path
  dirExists <- doesDirectoryExist dir
  isDir <- doesDirectoryExist path
  if
    | not dirExists ->
        pure (Left (FileError Writing path (MissingDirectory dir) ["peg-hs does not create directories; create " <> dir <> " first"]))
    | isDir -> pure (Left (FileError Writing path IsDirectory ["give the path of a file to write"]))
    | otherwise ->
        try (BS.writeFile path (TE.encodeUtf8 text)) >>= \case
          Right () -> pure (Right ())
          Left err -> Left <$> failure Writing path err

failure :: Access -> FilePath -> IOException -> IO FileError
failure access path err
  | isDoesNotExistError err = do
      let dir = takeDirectory path
      dirExists <- doesDirectoryExist dir
      cwd <- getCurrentDirectory
      pure $
        FileError access path NoSuchFile $
          ["the directory " <> dir <> " does not exist either" | not dirExists]
            ++ ["the path is relative to the current directory " <> cwd | isRelative path]
  | isPermissionError err = pure (FileError access path PermissionDenied [])
  | otherwise = pure (FileError access path (OtherError (show err)) [])

-- | The text of a file: UTF-8, without a byte order mark at the start; or
-- the position (from 1) of the first byte that is not UTF-8.
decodeUtf8File :: BS.ByteString -> Either Int Text
decodeUtf8File bytes0 =
  let bom = BS.pack [0xEF, 0xBB, 0xBF]
      (skipped, bytes) = if bom `BS.isPrefixOf` bytes0 then (3, BS.drop 3 bytes0) else (0, bytes0)
   in case utf8ErrorOffset bytes of
        Just n -> Left (skipped + n + 1)
        Nothing -> Right (TE.decodeUtf8 bytes)

-- | The offset (from 0) of the first ill-formed sequence of UTF-8, by the
-- table of well-formed byte sequences of the Unicode Standard (3.9, table
-- 3-7): no overlong forms, no surrogates, nothing above U+10FFFF.
utf8ErrorOffset :: BS.ByteString -> Maybe Int
utf8ErrorOffset bs = go 0
  where
    n = BS.length bs
    at i = if i < n then Just (BS.index bs i) else Nothing
    within :: Word8 -> Word8 -> Int -> Bool
    within lo hi i = maybe False (\b -> lo <= b && b <= hi) (at i)
    cont = within 0x80 0xBF
    go i
      | i >= n = Nothing
      | otherwise =
          let b = BS.index bs i
              ok k = go (i + k)
           in if
                | b <= 0x7F -> ok 1
                | 0xC2 <= b && b <= 0xDF, cont (i + 1) -> ok 2
                | b == 0xE0, within 0xA0 0xBF (i + 1), cont (i + 2) -> ok 3
                | (0xE1 <= b && b <= 0xEC) || b == 0xEE || b == 0xEF, cont (i + 1), cont (i + 2) -> ok 3
                | b == 0xED, within 0x80 0x9F (i + 1), cont (i + 2) -> ok 3
                | b == 0xF0, within 0x90 0xBF (i + 1), cont (i + 2), cont (i + 3) -> ok 4
                | 0xF1 <= b && b <= 0xF3, cont (i + 1), cont (i + 2), cont (i + 3) -> ok 4
                | b == 0xF4, within 0x80 0x8F (i + 1), cont (i + 2), cont (i + 3) -> ok 4
                | otherwise -> Just i

-- | Write standard output and standard error as UTF-8. Names of files that
-- the locale could not decode go out as their bytes.
setUtf8StdHandles :: IO ()
setUtf8StdHandles = do
  enc <- mkTextEncoding "UTF-8//ROUNDTRIP"
  hSetEncoding stdout enc
  hSetEncoding stderr enc
