module Main (main) where

import GHC (getSessionDynFlags, runGhc)
import GHC.Data.FastString (mkFastString)
import GHC.Data.StringBuffer (stringToStringBuffer)
import GHC.Driver.Config.Parser (initParserOpts)
import GHC.Parser.Lexer (P (..), ParseResult (..), getPsMessages, initParserState)
import GHC.Types.Error (isEmptyMessages)
import GHC.Types.SrcLoc (mkRealSrcLoc)
import PegTraceParser (parseModuleNoHaddock)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [libdir, file] -> do
      source <- readFile file
      result <- runGhc (Just libdir) $ do
        flags <- getSessionDynFlags
        let options = initParserOpts flags
            location = mkRealSrcLoc (mkFastString file) 1 1
            state = initParserState options (stringToStringBuffer source) location
        pure $ case unP parseModuleNoHaddock state of
          PFailed _ -> False
          POk parserState _ ->
            let (warnings, errors) = getPsMessages parserState
             in isEmptyMessages warnings && isEmptyMessages errors
      if result then putStrLn "parsed-no-diagnostics" else die "GHC parser failed or reported diagnostics"
    _ -> die "usage: TraceGeneratedModule LIBDIR GENERATED.hs"
