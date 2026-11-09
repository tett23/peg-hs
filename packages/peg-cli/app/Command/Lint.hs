-- | @peg-hs lint@: lint grammar files (ADR 0033).
module Command.Lint (lintCommand) where

import qualified Data.Text.IO as TIO
import Diagnostics (reportErrors)
import FileIO (readUtf8, reportFileError)
import Files (grammarFiles)
import Options
import Peg.Grammar.Check (check)
import Peg.Grammar.Lint (LintLevel (..), LintWarning (..), lintGrammar, renderLintWarning)
import Peg.Grammar
import Peg.Grammar.Import (libraryErrors, resolveImports)
import Peg.Grammar.Import.Files (readImports)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import System.Exit (ExitCode (..))
import System.IO (stderr)
import Data.Text (Text)

lintCommand :: Command
lintCommand =
  Command
    { cmdName = "lint"
    , cmdSummary = "lint grammars"
    , cmdArguments = "[FILE|DIR...]"
    , cmdDescription =
        [ "Check grammars against the fixed rules of peg-hs, and fail if there is a warning."
        , "The rules cannot be chosen or silenced; every warning goes away by changing the grammar."
        , "Infos, such as an action { () } that can be omitted, are shown only with --verbose,"
        , "and do not fail."
        , "A directory stands for the .hpeg files under it. Without arguments, lint every .hpeg"
        , "file under the current directory. Directories whose name starts with . and"
        , "dist-newstyle are skipped. Files are read as UTF-8."
        ]
    , cmdOptions =
        [ Opt "verbose" Nothing Nothing "also show the infos: what can be simpler, but is not wrong"
        ]
    , cmdExamples =
        [ ("peg-hs lint", "lint every grammar under the current directory")
        , ("peg-hs lint Expr.hpeg", "lint Expr.hpeg")
        , ("peg-hs lint --verbose Expr.hpeg", "lint Expr.hpeg, and show the infos too")
        ]
    , cmdRun = run
    }

run :: Parsed -> IO ExitCode
run p = do
  files <- grammarFiles (parsedArguments p)
  results <- mapM (lint (flag "verbose" p)) files
  pure (if and results then ExitSuccess else ExitFailure 1)

-- Lint one file; whether it has neither errors nor warnings. Infos do not
-- count, and are written only when verbose (ADR 0063, ADR 0067).
lint :: Bool -> FilePath -> IO Bool
lint verbose file =
  readUtf8 "" file >>= \case
    Left e -> reportFileError e >> pure False
    Right src -> lintText verbose file src

-- A library is checked on its own (ADR 0092). A grammar that imports
-- libraries is checked with their rules, and only the warnings in the
-- grammar itself are reported: those in a library are reported with the
-- library, once.
lintText :: Bool -> FilePath -> Text -> IO Bool
lintText verbose file src =
  case parseGrammar src of
    Left diags -> reportErrors file [] diags >> pure False
    Right g0
      | Just _ <- grammarLibrary g0 -> case libraryErrors g0 of
          [] -> report (lintGrammar g0)
          diags -> reportErrors file [] diags >> pure False
      | otherwise ->
          readImports file g0 >>= \texts ->
            case texts >>= resolveImports g0 >>= \g -> either (Left . templateNotes g) (const (Right g)) (expandTemplates g >>= check) of
              Left diags -> reportErrors file (grammarImports g0) diags >> pure False
              Right g -> report (filter ((== 0) . locFile . lintLoc) (lintGrammar g))
  where
    report ws = do
      let shown = if verbose then ws else filter ((/= LevelInfo) . lintLevel) ws
      mapM_ (TIO.hPutStrLn stderr . renderLintWarning file) shown
      pure (all ((== LevelInfo) . lintLevel) ws)
