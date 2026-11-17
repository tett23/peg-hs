-- Read a generated module with the tracing build of GHC 9.10.3's parser.
--
-- The flags are set as GHC's driver sets them for a module of the packages:
-- the language of the packages' default-language (GHC2021, the -X flag that
-- cabal passes), and then the module's own header pragmas (LANGUAGE and
-- OPTIONS_GHC), read with getOptions and applied with parseDynamicFilePragma.
-- The lexer and the parser both run under initParserOpts of those flags, so
-- an extension that %language names reaches them. With a third argument, the
-- tracer writes the header options to that file, one per line ("-XMagicHash"),
-- for check-trace-language.sh.
module Main (main) where

import Control.Monad (unless)
import GHC (getSessionDynFlags, runGhc)
import GHC.Data.FastString (mkFastString)
import GHC.Data.StringBuffer (stringToStringBuffer)
import GHC.Driver.Config.Parser (initParserOpts)
import GHC.Driver.Session (parseDynamicFilePragma, parseDynamicFlagsCmdLine)
import GHC.Parser.Header (getOptions)
import GHC.Parser.Lexer (P (..), ParseResult (..), getPsMessages, initParserState)
import GHC.Types.Error (isEmptyMessages)
import GHC.Types.SrcLoc (mkRealSrcLoc, noLoc, unLoc)
import PegTraceParser (parseModuleNoHaddock)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  args <- getArgs
  case args of
    libdir : file : optionsFile | length optionsFile <= 1 -> do
      source <- readFile file
      let buffer = stringToStringBuffer source
      outcome <- runGhc (Just libdir) $ do
        session <- getSessionDynFlags
        (base, baseLeft, baseMessages) <- parseDynamicFlagsCmdLine session [noLoc "-XGHC2021"]
        let (headerMessages, options) = getOptions (initParserOpts base) buffer file
        (flags, left, pragmaMessages) <- parseDynamicFilePragma base options
        let clean =
              null baseLeft && null left && isEmptyMessages baseMessages
                && isEmptyMessages headerMessages && isEmptyMessages pragmaMessages
            location = mkRealSrcLoc (mkFastString file) 1 1
            state = initParserState (initParserOpts flags) buffer location
            parsed = case unP parseModuleNoHaddock state of
              PFailed _ -> False
              POk parserState _ ->
                let (warnings, errors) = getPsMessages parserState
                 in isEmptyMessages warnings && isEmptyMessages errors
        pure (map unLoc options, clean, parsed)
      let (options, clean, parsed) = outcome
      mapM_ (\path -> writeFile path (unlines options)) optionsFile
      unless clean $ die "GHC did not take the header pragmas of the module"
      if parsed then putStrLn "parsed-no-diagnostics" else die "GHC parser failed or reported diagnostics"
    _ -> die "usage: TraceGeneratedModule LIBDIR GENERATED.hs [OPTIONS-OUTPUT]"
