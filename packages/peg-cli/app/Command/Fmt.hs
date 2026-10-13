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
    , cmdArguments = "[FILE...]"
    , cmdDescription =
        [ "Format grammars in place, in the one style of peg-hs."
        , "Without files, format every .peg file under the current directory,"
        , "except in directories whose name starts with . and dist-newstyle."
        ]
    , cmdOptions =
        [ Opt "check" Nothing Nothing "write nothing; list the files that are not formatted and fail if any"
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
