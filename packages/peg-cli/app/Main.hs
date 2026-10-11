{-# LANGUAGE OverloadedStrings #-}

-- | @peg-hs@: generate a Haskell module from a @.peg@ grammar.
module Main (main) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Codegen
import Peg.Grammar (renderDiagnostic)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (replaceExtension)
import System.IO (hPutStrLn, stderr)

data Args = Args
  { argInput :: Maybe FilePath
  , argOutput :: Maybe FilePath
  , argDebug :: Bool
  }

usage :: String
usage =
  unlines
    [ "usage: peg-hs INPUT.peg [-o OUTPUT.hs] [--debug-entry]"
    , ""
    , "Generate a Haskell module from a peg-hs grammar."
    , "The output defaults to the input path with the extension .hs."
    , ""
    , "  -o, --output FILE  write the module to FILE"
    , "  --debug-entry      also export peg'parseWith (for testing the generator)"
    , "  -h, --help         show this help"
    ]

parseArgs :: [String] -> Either String Args
parseArgs = go (Args Nothing Nothing False)
  where
    go a [] = Right a
    go a (flag : file : rest)
      | flag `elem` ["-o", "--output"] = go a {argOutput = Just file} rest
    go a (flag : rest)
      | flag == "--debug-entry" = go a {argDebug = True} rest
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
    Right (Args (Just input) output debug) -> do
      let out = maybe (replaceExtension input "hs") id output
          opts = Options {optSourceName = input, optOutputName = out, optDebugEntry = debug}
      src <- TIO.readFile input
      case generateFromSource opts src of
        Left diags -> do
          mapM_ (TIO.hPutStrLn stderr . renderDiagnostic input) diags
          exitFailure
        Right code -> TIO.writeFile out code >> putStrLn ("wrote " <> out <> " (" <> show (T.length code) <> " characters)")
