-- | Writing diagnostics to stderr, as @file:line:column: error: message@
-- and @file:line:column: warning: message@ (ADR 0037).
module Diagnostics
  ( reportErrors
  , reportWarnings
  ) where

import qualified Data.Text.IO as TIO
import Peg.Codegen (renderWarning)
import Peg.Grammar (Diagnostic, renderDiagnostic)
import System.IO (stderr)

reportErrors :: FilePath -> [Diagnostic] -> IO ()
reportErrors file = mapM_ (TIO.hPutStrLn stderr . renderDiagnostic file)

reportWarnings :: FilePath -> [Diagnostic] -> IO ()
reportWarnings file = mapM_ (TIO.hPutStrLn stderr . renderWarning file)
