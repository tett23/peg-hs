{-# LANGUAGE OverloadedStrings #-}

-- | Writing diagnostics to stderr, as @file:line:column: error: message@
-- and @file:line:column: warning: message@ (ADR 0037).
module Diagnostics
  ( reportErrors
  , reportWarnings
  , renderWarning
  ) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Grammar (Diagnostic (..), Loc (..), renderDiagnostic)
import System.IO (stderr)

reportErrors :: FilePath -> [Diagnostic] -> IO ()
reportErrors file = mapM_ (TIO.hPutStrLn stderr . renderDiagnostic file)

reportWarnings :: FilePath -> [Diagnostic] -> IO ()
reportWarnings file = mapM_ (TIO.hPutStrLn stderr . renderWarning file)

-- | Like 'renderDiagnostic', for a warning.
renderWarning :: FilePath -> Diagnostic -> T.Text
renderWarning file (Diagnostic (Loc l c) msg) =
  T.pack file <> ":" <> T.pack (show l) <> ":" <> T.pack (show c) <> ": warning: " <> msg
