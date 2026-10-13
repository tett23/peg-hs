-- | @peg-hs fmt@: format grammar files (ADR 0032).
module Command.Fmt (fmtCommand) where

import Diagnostics (reportErrors)
import FileIO (readUtf8, reportFileError, writeUtf8)
import Files (grammarFiles)
import Options
import Peg.Grammar.Format (formatGrammar)
import System.Exit (ExitCode (..))

fmtCommand :: Command
fmtCommand =
  Command
    { cmdName = "fmt"
    , cmdSummary = "format grammars"
    , cmdArguments = "[FILE|DIR...]"
    , cmdDescription =
        [ "Format grammars in place, in the one style of peg-hs. Comments are kept."
        , "A directory stands for the .peg files under it. Without arguments, format every .peg"
        , "file under the current directory. Directories whose name starts with . and"
        , "dist-newstyle are skipped. Files are read and written as UTF-8."
        ]
    , cmdOptions =
        [ Opt "check" Nothing Nothing "write nothing; list the files that are not formatted and fail if any"
        ]
    , cmdExamples =
        [ ("peg-hs fmt", "format every grammar under the current directory")
        , ("peg-hs fmt --check grammar", "list the grammars under grammar that are not formatted, and fail if any")
        ]
    , cmdRun = run
    }

run :: Parsed -> IO ExitCode
run p = do
  files <- grammarFiles (parsedArguments p)
  results <- mapM (format (flag "check" p)) files
  pure (if and results then ExitSuccess else ExitFailure 1)

-- Format one file; whether it was formatted (or, with --check, already was).
format :: Bool -> FilePath -> IO Bool
format checkOnly file =
  readUtf8 "" file >>= \case
    Left e -> reportFileError e >> pure False
    Right src -> case formatGrammar src of
      Left diags -> reportErrors file diags >> pure False
      Right out
        | out == src -> pure True
        | checkOnly -> putStrLn file >> pure False
        | otherwise -> writeUtf8 file out >>= either (\e -> reportFileError e >> pure False) (const (pure True))
