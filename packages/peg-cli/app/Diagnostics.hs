-- | Writing diagnostics to stderr, as @file:line:column: error: message@
-- and @file:line:column: warning: message@ (ADR 0037). The file is the
-- grammar given, or a library that it imports (ADR 0092), named by the
-- @%import@s of the grammar.
module Diagnostics
  ( reportErrors
  , reportWarnings
  ) where

import qualified Data.Text.IO as TIO
import Peg.Codegen (renderWarning)
import Peg.Grammar (Diagnostic, Located, renderDiagnostic)
import System.IO (stderr)

reportErrors :: FilePath -> [Located FilePath] -> [Diagnostic] -> IO ()
reportErrors file imports = mapM_ (TIO.hPutStrLn stderr . renderDiagnostic file imports)

reportWarnings :: FilePath -> [Located FilePath] -> [Diagnostic] -> IO ()
reportWarnings file imports = mapM_ (TIO.hPutStrLn stderr . renderWarning file imports)
