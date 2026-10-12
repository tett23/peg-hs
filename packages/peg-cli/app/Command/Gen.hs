{-# LANGUAGE OverloadedStrings #-}

-- | @peg-hs gen@: generate a Haskell module from a grammar.
module Command.Gen (genCommand) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Diagnostics (reportErrors, reportWarnings)
import Options
import Peg.Codegen
import Peg.Grammar.Check (check)
import Peg.Grammar.Labels (labelWarnings, stripLabelsAs)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import System.Exit (ExitCode (..))
import System.FilePath (replaceExtension)

genCommand :: Command
genCommand =
  Command
    { cmdName = "gen"
    , cmdSummary = "generate a Haskell module from a grammar"
    , cmdArguments = "GRAMMAR.peg"
    , cmdDescription =
        [ "Generate a Haskell module from a grammar."
        , "The output defaults to the grammar's path with the extension .hs."
        ]
    , cmdOptions =
        [ Opt "output" (Just 'o') (Just "FILE") "write the module to FILE"
        , Opt "debug-entry" Nothing Nothing "also export peg'parseWith (for testing the generator)"
        , Opt "Werror" Nothing Nothing "fail if there are warnings"
        , Opt "strip-labels" Nothing (Just "MODULE") "generate the grammar without its labels as MODULE (for testing that the labels are safe)"
        ]
    , cmdRun = run
    }

run :: Parsed -> IO ExitCode
run p = case parsedArguments p of
  [input] -> do
    let out = maybe (replaceExtension input "hs") id (value "output" p)
        opts = Options {optSourceName = input, optOutputName = out, optDebugEntry = flag "debug-entry" p}
        strip = value "strip-labels" p
    src <- TIO.readFile input
    case parseGrammar src >>= \g0 -> either (Left . templateNotes g0) (Right . (,) g0) (expandTemplates g0 >>= \g -> g <$ check g) of
      Left diags -> reportErrors input diags >> pure (ExitFailure 1)
      Right (g0, g) -> do
        let warnings = if strip == Nothing then templateNotes g0 (labelWarnings g) else []
            target = maybe g (\m -> stripLabelsAs (T.pack m) g) strip
        reportWarnings input warnings
        if flag "Werror" p && not (null warnings)
          then pure (ExitFailure 1)
          else case generate opts target of
            Left diags -> reportErrors input diags >> pure (ExitFailure 1)
            Right code -> do
              TIO.writeFile out code
              putStrLn ("wrote " <> out <> " (" <> show (T.length code) <> " characters)")
              pure ExitSuccess
  [] -> usageError "gen needs a grammar file"
  _ -> usageError "gen takes one grammar file"
