{-# LANGUAGE OverloadedStrings #-}

-- | @peg-hs@: generate a Haskell module from a @.peg@ grammar.
module Main (main) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Codegen
import Peg.Grammar (Diagnostic (..), Loc (..), renderDiagnostic)
import Peg.Grammar.Check (check)
import Peg.Grammar.Labels (labelWarnings, stripLabelsAs)
import Peg.Grammar.Parser (parseGrammar)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (replaceExtension)
import System.IO (hPutStrLn, stderr)

data Args = Args
  { argInput :: Maybe FilePath
  , argOutput :: Maybe FilePath
  , argDebug :: Bool
  , argWerror :: Bool
  , argStripLabels :: Maybe String
  }

usage :: String
usage =
  unlines
    [ "usage: peg-hs INPUT.peg [-o OUTPUT.hs] [--debug-entry] [--Werror] [--strip-labels MODULE]"
    , ""
    , "Generate a Haskell module from a peg-hs grammar."
    , "The output defaults to the input path with the extension .hs."
    , ""
    , "  -o, --output FILE  write the module to FILE"
    , "  --debug-entry      also export peg'parseWith (for testing the generator)"
    , "  --Werror           fail if there are warnings"
    , "  --strip-labels MODULE"
    , "                     generate the grammar without its labels as MODULE"
    , "                     (for testing that the labels are safe)"
    , "  -h, --help         show this help"
    ]

parseArgs :: [String] -> Either String Args
parseArgs = go (Args Nothing Nothing False False Nothing)
  where
    go a [] = Right a
    go a (flag : file : rest)
      | flag `elem` ["-o", "--output"] = go a {argOutput = Just file} rest
      | flag == "--strip-labels" = go a {argStripLabels = Just file} rest
    go a (flag : rest)
      | flag == "--debug-entry" = go a {argDebug = True} rest
      | flag == "--Werror" = go a {argWerror = True} rest
      | flag `elem` ["-h", "--help"] = Left usage
      | take 1 flag == "-" = Left ("unknown option " <> flag <> "\n\n" <> usage)
      | otherwise = case argInput a of
          Nothing -> go a {argInput = Just flag} rest
          Just _ -> Left ("more than one input file\n\n" <> usage)

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Left msg -> hPutStrLn stderr msg >> exitFailure
    Right Args {argInput = Nothing} -> hPutStrLn stderr usage >> exitFailure
    Right (Args (Just input) output debug werror strip) -> do
      let out = maybe (replaceExtension input "hs") id output
          opts = Options {optSourceName = input, optOutputName = out, optDebugEntry = debug}
          failWith diags = mapM_ (TIO.hPutStrLn stderr . renderDiagnostic input) diags >> exitFailure
      src <- TIO.readFile input
      case parseGrammar src >>= \g -> g <$ check g of
        Left diags -> failWith diags
        Right g -> do
          let warnings = if strip == Nothing then labelWarnings g else []
              target = maybe g (\m -> stripLabelsAs (T.pack m) g) strip
          mapM_ (TIO.hPutStrLn stderr . renderWarning input) warnings
          if werror && not (null warnings)
            then exitFailure
            else case generate opts target of
              Left diags -> failWith diags
              Right code -> TIO.writeFile out code >> putStrLn ("wrote " <> out <> " (" <> show (T.length code) <> " characters)")

-- Like 'renderDiagnostic', for a warning.
renderWarning :: FilePath -> Diagnostic -> T.Text
renderWarning file (Diagnostic (Loc l c) msg) =
  T.pack file <> ":" <> T.pack (show l) <> ":" <> T.pack (show c) <> ": warning: " <> msg
