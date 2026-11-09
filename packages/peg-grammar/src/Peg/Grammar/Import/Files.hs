{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Reading the libraries that a grammar imports (ADR 0092). @peg-hs@, the
-- setup hooks of peg-hooks and the language server read them with these
-- functions, and give the texts to 'Peg.Grammar.Import.resolveImports'.
--
-- A path of @%import@ is relative to the directory of the grammar, and
-- has no @..@ ('Peg.Grammar.Assemble.isImportPath'), so only files in that
-- directory and under it are read. No part of the path may be a symbolic
-- link: a link is not followed, as the walk of @peg-hs fmt@ and
-- @peg-hs lint@ does not follow one (ADR 0077), since the grammar names
-- the file, not the user. A file is read as UTF-8, without a byte order
-- mark at its start.
module Peg.Grammar.Import.Files
  ( readImports
  , readImport
  , readLibrary
  ) where

import Control.Exception (IOException, try)
import qualified Data.ByteString as BS
import Data.Either (partitionEithers)
import Data.List (inits)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Peg.Grammar
import System.Directory (doesFileExist, pathIsSymbolicLink)
import System.FilePath (joinPath, splitDirectories, takeDirectory, (</>))
import System.IO.Error (isPermissionError)

-- | The texts of the libraries that a grammar imports, given the path of
-- the grammar, as 'Peg.Grammar.Import.resolveImports' takes them; or the
-- errors of the files that cannot be read ('readImport'), at their
-- @%import@s.
readImports :: FilePath -> Grammar -> IO (Either [Diagnostic] [(FilePath, Text)])
readImports file g = do
  results <- mapM (\i -> fmap ((,) (unLoc i)) <$> readImport (takeDirectory file) i) (grammarImports g)
  pure $ case partitionEithers results of
    ([], texts) -> Right texts
    (errs, _) -> Left errs

-- | The text of a library, given the directory of the grammar and the path
-- of its @%import@; or an error at the @%import@:
-- @cannot import lex\/Ident.hpeg: it is a symbolic link@ when a part of the
-- path is a link, @cannot import lex\/Ident.hpeg: no such file@ when there
-- is no file, and @not UTF-8@ or @permission denied@ in place of
-- @no such file@ when it cannot be read.
readImport :: FilePath -> Located FilePath -> IO (Either Diagnostic Text)
readImport dir (Located l p) = either (\reason -> Left (Diagnostic l ("cannot import " <> T.pack p <> ": " <> reason))) Right <$> readLibrary dir p

-- | The text of a library, given the directory of the grammar and the path
-- of its @%import@, which has the form of
-- 'Peg.Grammar.Assemble.isImportPath'; or why it cannot be read:
-- @it is a symbolic link@, @no such file@, @permission denied@ or
-- @not UTF-8@. The language server reads the libraries that are not open
-- with it.
readLibrary :: FilePath -> FilePath -> IO (Either Text Text)
readLibrary dir p = do
  links <- mapM isLink [dir </> joinPath ps | ps <- drop 1 (inits (splitDirectories p))]
  if or links
    then pure (Left "it is a symbolic link")
    else do
      let path = dir </> p
      exists <- doesFileExist path
      if not exists
        then pure (Left "no such file")
        else
          try (BS.readFile path) >>= \case
            Left (e :: IOException)
              | isPermissionError e -> pure (Left "permission denied")
              | otherwise -> pure (Left "no such file")
            Right bytes -> pure $ case TE.decodeUtf8' (dropBom bytes) of
              Left _ -> Left "not UTF-8"
              Right t -> Right t
  where
    isLink path = either (\(_ :: IOException) -> False) id <$> try (pathIsSymbolicLink path)
    dropBom b = if BS.pack [0xEF, 0xBB, 0xBF] `BS.isPrefixOf` b then BS.drop 3 b else b
