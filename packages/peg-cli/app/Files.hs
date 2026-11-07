{-# LANGUAGE MultiWayIf #-}

-- | The grammar files of a command that takes files or, with none, every
-- @.hpeg@ file under the current directory (ADR 0032). A directory among the
-- files stands for the @.hpeg@ files under it (ADR 0045). Files with the
-- old extension @.peg@ are not looked for, since other tools use it too; a
-- file given by name is taken whatever its extension (ADR 0050).
--
-- The walk does not follow symbolic links, to files or to directories
-- (ADR 0077): it stays inside the directory it starts from, and ends on
-- cyclic links. A file given by name is read and written through its link,
-- and a directory given by name is walked even if it is a link.
module Files (grammarFiles) where

import Data.List (isPrefixOf, sort)
import System.Directory (doesDirectoryExist, listDirectory, pathIsSymbolicLink)
import System.FilePath (takeExtension, takeFileName, (</>))

-- | The given files, or the @.hpeg@ files found by walking the current
-- directory, skipping symbolic links and directories whose name starts
-- with @.@ and @dist-newstyle@, in the order of their paths. A given
-- directory is walked in the same way.
grammarFiles :: [FilePath] -> IO [FilePath]
grammarFiles [] = sort <$> walk Nothing
grammarFiles files = concat <$> mapM expand files
  where
    expand f = do
      isDir <- doesDirectoryExist f
      if isDir then sort <$> walk (Just f) else pure [f]

walk :: Maybe FilePath -> IO [FilePath]
walk dir = do
  names <- sort <$> listDirectory (maybe "." id dir)
  concat <$> mapM visit names
  where
    visit name = do
      let path = maybe name (</> name) dir
      isLink <- pathIsSymbolicLink path
      isDir <- if isLink then pure False else doesDirectoryExist path
      if
        | isLink -> pure []
        | isDir -> if skipped name then pure [] else walk (Just path)
        | otherwise -> pure [path | takeExtension name == ".hpeg"]
    skipped name = "." `isPrefixOf` takeFileName name || name == "dist-newstyle"
