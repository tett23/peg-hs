{-# LANGUAGE OverloadedStrings #-}

-- | @peg-hs gen@: generate a Haskell module from a grammar.
module Command.Gen (genCommand) where

import qualified Data.Text as T
import Diagnostics (reportErrors, reportWarnings)
import FileIO (readUtf8, reportFileError, writeUtf8)
import Options
import Peg.Codegen
import Peg.Grammar (grammarImports)
import Peg.Grammar.Import.Files (readImports)
import Peg.Grammar.Parser (parseGrammar)
import System.Exit (ExitCode (..))
import System.FilePath (replaceExtension)

genCommand :: Command
genCommand =
  Command
    { cmdName = "gen"
    , cmdSummary = "generate a Haskell module from a grammar"
    , cmdArguments = "GRAMMAR.hpeg"
    , cmdDescription =
        [ "Generate a Haskell module from a grammar. The module depends only on the package"
        , "peg-runtime. The output defaults to the grammar's path with the extension .hs."
        , ""
        , "The module records the paths given here, in its header and in LINE pragmas that point"
        , "the errors of GHC at the grammar. Give the paths relative to the directory of the package"
        , "that compiles the module: editors can then open them, and the module is the same on"
        , "every machine. Files are read and written as UTF-8."
        , ""
        , "The module exports the entry points (parse, and parseSyntax, parseRecover and"
        , "parseSyntaxRecover when the grammar has them), the names of %syntax and the names of %export."
        , "With --export, it exports only the names given of the first two kinds, always with the names"
        , "of %export, and leaves out the declarations that only the other names use. A type wrapper"
        , "is given without (..). A name the generator does not define is an error."
        ]
    , cmdOptions =
        [ Opt "output" (Just 'o') (Just "FILE") "write the module to FILE"
        , Opt "export" Nothing (Just "NAME") "export only NAME of the names the generator defines; can be given more than once"
        , Opt "debug-entry" Nothing Nothing "also export peg'parseWith (for testing the generator)"
        , Opt "Werror" Nothing Nothing "fail if there are warnings"
        , Opt "strip-labels" Nothing (Just "MODULE") "generate the grammar without its labels as MODULE (for testing that the labels are safe)"
        ]
    , cmdExamples =
        [ ("peg-hs gen grammar/Expr.hpeg -o src/Expr/Parser.hs", "generate src/Expr/Parser.hs from grammar/Expr.hpeg")
        , ("peg-hs gen --Werror Expr.hpeg", "generate Expr.hs, and fail if a label may reject valid input")
        , ("peg-hs gen --export parseSyntaxRecover --export nameOfSyntaxKind Doc.hpeg", "generate Doc.hs that exports only parseSyntaxRecover, nameOfSyntaxKind and the names of %export")
        ]
    , cmdRun = run
    }

run :: Parsed -> IO ExitCode
run p = case parsedArguments p of
  [input] -> do
    let out = maybe (replaceExtension input "hs") id (value "output" p)
        opts = Options {optSourceName = input, optOutputName = out, optDebugEntry = flag "debug-entry" p, optExports = exports}
        exports = case [T.pack x | ("export", x) <- parsedOptions p] of
          [] -> Nothing
          xs -> Just xs
        strip = value "strip-labels" p
    readUtf8 "peg-hs gen takes a grammar file, not a directory" input >>= \case
      Left e -> reportFileError e >> pure (ExitFailure 1)
      Right src -> generateFrom input out opts strip p src
  [] -> commandUsageError "gen" "gen needs a grammar file"
  _ -> commandUsageError "gen" "gen takes one grammar file"

-- The libraries of the grammar are read first (ADR 0092).
generateFrom :: FilePath -> FilePath -> Options -> Maybe String -> Parsed -> T.Text -> IO ExitCode
generateFrom input out opts strip p src =
  libraries >>= \case
    Left (imports, diags) -> reportErrors input imports diags >> pure (ExitFailure 1)
    Right (imports, texts) -> case generateWithWarnings opts (T.pack <$> strip) texts src of
      Left diags -> reportErrors input imports diags >> pure (ExitFailure 1)
      Right gen -> written imports gen
  where
    libraries = case parseGrammar src of
      Left diags -> pure (Left ([], diags))
      Right g -> either (\ds -> Left (grammarImports g, ds)) (\ts -> Right (grammarImports g, ts)) <$> readImports input g
    written imports gen = do
      let warnings = generationWarnings gen
      reportWarnings input imports warnings
      if flag "Werror" p && not (null warnings)
        then pure (ExitFailure 1)
        else case generationModule gen of
          Left diags -> reportErrors input imports diags >> pure (ExitFailure 1)
          Right code ->
            writeUtf8 out code >>= \case
              Left e -> reportFileError e >> pure (ExitFailure 1)
              Right () -> do
                putStrLn ("wrote " <> out <> " (" <> show (T.length code) <> " characters)")
                pure ExitSuccess
