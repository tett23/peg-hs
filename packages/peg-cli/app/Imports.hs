-- | Reading a grammar with the libraries it imports (ADR 0092), for the
-- commands that check a grammar as @peg-hs gen@ does.
module Imports
  ( Loaded (..)
  , loadGrammar
  ) where

import Data.Text (Text)
import Peg.Grammar
import Peg.Grammar.Import (resolveImports)
import Peg.Grammar.Import.Files (readImports)
import Peg.Grammar.Parser (parseGrammar)

-- | A grammar with the rules of its libraries, and the texts of the
-- libraries by the paths of the @%import@s.
data Loaded = Loaded
  { loadedGrammar :: Grammar
  , loadedLibraries :: [(FilePath, Text)]
  }

-- | Parse a grammar read from the path given, read the libraries it
-- imports and put their rules into it. The errors come with the
-- @%import@s of the grammar, which name the files of their locations;
-- there are none when the grammar does not parse.
loadGrammar :: FilePath -> Text -> IO (Either ([Located FilePath], [Diagnostic]) Loaded)
loadGrammar file src = case parseGrammar src of
  Left ds -> pure (Left ([], ds))
  Right g0 -> do
    let imports = grammarImports g0
    texts <- readImports file g0
    pure $ case texts >>= \ts -> (\g -> Loaded g ts) <$> resolveImports g0 ts of
      Left ds -> Left (imports, ds)
      Right loaded -> Right loaded
