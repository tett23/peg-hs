-- | @peg-hs lint@: lint grammar files (ADR 0033).
module Command.Lint (lintCommand) where

import qualified Data.Text.IO as TIO
import Diagnostics (reportErrors)
import FileIO (readUtf8, reportFileError)
import Files (grammarFiles)
import Options
import Peg.Grammar.Check (check)
import Peg.Grammar.Lint (lintGrammar, renderLintWarning)
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
    , cmdArguments = "[FILE...]"
    , cmdDescription =
        [ "Check grammars against the fixed rules of peg-hs, and fail if there is a warning."
        , "The rules cannot be chosen or silenced; every warning goes away by changing the grammar."
        , "Without files, lint every .peg file under the current directory,"
        , "except in directories whose name starts with . and dist-newstyle."
        ]
    , cmdOptions = []
    , cmdRun = run
    }

run :: Parsed -> IO ExitCode
run p = do
  files <- grammarFiles (parsedArguments p)
  results <- mapM lint files
  pure (if and results then ExitSuccess else ExitFailure 1)

-- Lint one file; whether it has neither errors nor warnings.
lint :: FilePath -> IO Bool
lint file =
  readUtf8 "" file >>= \case
    Left e -> reportFileError e >> pure False
    Right src -> lintText file src

lintText :: FilePath -> Text -> IO Bool
lintText file src =
  case parseGrammar src >>= \g -> either (Left . templateNotes g) (const (Right g)) (expandTemplates g >>= check) of
    Left diags -> reportErrors file diags >> pure False
    Right g -> case lintGrammar g of
      [] -> pure True
      ws -> mapM_ (TIO.hPutStrLn stderr . renderLintWarning file) ws >> pure False
