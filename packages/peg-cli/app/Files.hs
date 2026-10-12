-- | The grammar files of a command that takes files or, with none, every
-- @.peg@ file under the current directory (ADR 0032).
module Files (grammarFiles) where

import Data.List (isPrefixOf, sort)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeExtension, takeFileName, (</>))

-- | The given files, or the @.peg@ files found by walking the current
-- directory, skipping directories whose name starts with @.@ and
-- @dist-newstyle@, in the order of their paths.
grammarFiles :: [FilePath] -> IO [FilePath]
grammarFiles [] = sort <$> walk Nothing
grammarFiles files = pure files

walk :: Maybe FilePath -> IO [FilePath]
walk dir = do
  names <- sort <$> listDirectory (maybe "." id dir)
  concat <$> mapM visit names
  where
    visit name = do
      let path = maybe name (</> name) dir
      isDir <- doesDirectoryExist path
      if isDir
        then if skipped name then pure [] else walk (Just path)
        else pure [path | takeExtension name == ".peg"]
    skipped name = "." `isPrefixOf` takeFileName name || name == "dist-newstyle"
