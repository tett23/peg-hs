{-# LANGUAGE OverloadedStrings #-}

-- | @peg-hs parse@: parse an input with a grammar and show its AST and CST
-- (ADR 0036). The parser generated from the grammar is compiled with GHC,
-- together with the embedded sources of peg-runtime, and the executable is
-- cached.
module Command.Parse (parseCommand, fnv1a) where

import Control.Monad (forM_, unless, when)
import Data.Bits (xor)
import qualified Data.ByteString as BS
import Data.Char (isSpace)
import Data.List (intercalate, isInfixOf, isPrefixOf)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Data.Version (showVersion)
import Data.Word (Word64)
import Diagnostics (reportErrors)
import Embedded (prettySource, runtimeSources)
import GHC.Clock (getMonotonicTimeNSec)
import Numeric (showHex)
import Options
import Paths_peg_cli (version)
import Peg.Codegen (Options (..), generate)
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import System.Directory
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import System.IO (hPutStr, hPutStrLn, stderr)
import System.Process (readProcessWithExitCode)

parseCommand :: Command
parseCommand =
  Command
    { cmdName = "parse"
    , cmdSummary = "parse an input with a grammar and show its AST and CST"
    , cmdArguments = "GRAMMAR.peg INPUT"
    , cmdDescription =
        [ "Parse INPUT with the grammar and show the value of the start rule (the AST)"
        , "or the lossless syntax tree (the CST). The parser is compiled with the ghc on PATH,"
        , "and cached under $XDG_CACHE_HOME/peg-hs/parse. The AST needs a Show instance of"
        , "the type of the start rule. Run through cabal exec to use the packages of a project."
        ]
    , cmdOptions =
        [ Opt "format" Nothing (Just "ast|cst|all") "what to show (default: ast)"
        , Opt "entry" Nothing (Just "RULE") "parse with a rule of %entry instead of the start rule"
        , Opt "ghc-arg" Nothing (Just "ARG") "pass ARG to ghc, such as -isrc (repeatable)"
        ]
    , cmdRun = run
    }

data Format = Ast | Cst | All
  deriving (Eq)

run :: Parsed -> IO ExitCode
run p = case (parsedArguments p, value "format" p) of
  ([grammarFile, input], fmt)
    | Just format <- maybe (Just Ast) formatOf fmt -> parseWith grammarFile input format (value "entry" p) [v | ("ghc-arg", v) <- parsedOptions p]
    | otherwise -> usageError "--format takes ast, cst or all"
  ([_], _) -> usageError "parse needs a grammar file and an input file"
  ([], _) -> usageError "parse needs a grammar file and an input file"
  _ -> usageError "parse takes a grammar file and an input file"
  where
    formatOf = \case
      "ast" -> Just Ast
      "cst" -> Just Cst
      "all" -> Just All
      _ -> Nothing

parseWith :: FilePath -> FilePath -> Format -> Maybe String -> [String] -> IO ExitCode
parseWith grammarFile input format entry ghcArgs = do
  src <- TIO.readFile grammarFile
  case parseGrammar src >>= \g0 -> either (Left . templateNotes g0) (const (Right g0)) (expandTemplates g0 >>= check) of
    Left diags -> reportErrors grammarFile diags >> pure (ExitFailure 1)
    Right g
      | isJust (grammarEnv g) -> failWith (grammarFile <> ": peg-hs parse does not support grammars with %env")
      | Just e <- entry, T.pack e `notElem` map unLoc (grammarEntries g) -> failWith (grammarFile <> ": " <> e <> " is not a rule of %entry")
      | otherwise ->
          findExecutable "ghc" >>= \case
            Nothing -> failWith "peg-hs parse needs ghc on PATH"
            Just _ -> do
              (_, out, _) <- readProcessWithExitCode "ghc" ["--numeric-version"] ""
              let ghcVersion = takeWhile (not . isSpace) out
              if not ("9.10." `isPrefixOf` ghcVersion)
                then failWith ("peg-hs parse needs GHC 9.10, the versions peg-runtime supports (base 4.20); ghc is " <> ghcVersion)
                else do
                  dir <- cacheDir (T.unpack src) entry ghcArgs ghcVersion
                  let withAst = format /= Cst
                  let exe = parserPath dir withAst
                  built <- doesFileExist exe
                  ok <-
                    if built
                      then pure True
                      else build grammarFile g dir withAst entry ghcArgs
                  if not ok
                    then pure (ExitFailure 1)
                    else do
                      (code, out', err) <- readProcessWithExitCode exe [modeArg format, input] ""
                      putStr out'
                      hPutStr stderr err
                      pure code
  where
    failWith msg = hPutStrLn stderr ("peg-hs: " <> msg) >> pure (ExitFailure 1)
    modeArg = \case
      Ast -> "ast"
      Cst -> "cst"
      All -> "all"

-- The cache directory for a grammar, the options and the versions.
cacheDir :: String -> Maybe String -> [String] -> String -> IO FilePath
cacheDir src entry ghcArgs ghcVersion = do
  base <- lookupEnv "XDG_CACHE_HOME" >>= \case
    Just d | not (null d) -> pure d
    _ -> (</> ".cache") <$> getHomeDirectory
  let key = intercalate "\0" [src, fromMaybe "" entry, intercalate "\1" ghcArgs, showVersion version, ghcVersion]
  pure (base </> "peg-hs" </> "parse" </> fnv1a key)

-- An executable that shows the AST, the CST or both; one without the AST
-- needs no Show instance.
parserPath :: FilePath -> Bool -> FilePath
parserPath dir withAst = dir </> (if withAst then "parse-ast" else "parse-cst")

-- | The 64-bit FNV-1a hash of the UTF-8 encoding of a string, in hex.
fnv1a :: String -> String
fnv1a s =
  let h = BS.foldl' (\acc b -> (acc `xor` fromIntegral b) * 1099511628211) (14695981039346656037 :: Word64) (TE.encodeUtf8 (T.pack s))
      hex = showHex h ""
   in replicate (16 - length hex) '0' <> hex

-- Write the sources to a temporary directory and compile them into the
-- cache; report GHC's errors.
build :: FilePath -> Grammar -> FilePath -> Bool -> Maybe String -> [String] -> IO Bool
build grammarFile g dir withAst entry ghcArgs = do
  tmp <- getTemporaryDirectory
  stamp <- getMonotonicTimeNSec
  let work = tmp </> ("peg-hs-parse-" <> show stamp)
      srcDir = work </> "src"
      moduleName = T.unpack (unLoc (grammarModule g))
      modulePath = srcDir </> map (\c -> if c == '.' then '/' else c) moduleName <> ".hs"
      syntaxGrammar = g {grammarSyntax = Just (fromMaybe (Loc 1 1) (grammarSyntax g))}
      opts = Options {optSourceName = grammarFile, optOutputName = modulePath, optDebugEntry = False}
  case generate opts syntaxGrammar of
    Left diags -> reportErrors grammarFile diags >> pure False
    Right code -> do
      createDirectoryIfMissing True (takeDirectory modulePath)
      TIO.writeFile modulePath code
      forM_ runtimeSources $ \(path, text) -> do
        createDirectoryIfMissing True (takeDirectory (srcDir </> path))
        writeFile (srcDir </> path) text
      writeFile (srcDir </> "Pretty.hs") prettySource
      writeFile (srcDir </> "Main.hs") (mainSource moduleName withAst entry)
      createDirectoryIfMissing True dir
      let exe = parserPath dir withAst
      (status, out, err) <-
        readProcessWithExitCode "ghc" (["--make", "-O0", "-v0", "-i" <> srcDir, "-outputdir", work </> "build", "-o", work </> "parser", srcDir </> "Main.hs"] ++ ghcArgs) ""
      -- Another peg-hs may be building the same parser: the executable
      -- appears in the cache at once, by a rename.
      when (status == ExitSuccess) $ renameFile (work </> "parser") exe
      removeDirectoryRecursive work
      unless (status == ExitSuccess) $ do
        hPutStr stderr (out <> err)
        when (withAst && "Show" `isInfixOf` err && "No instance" `isInfixOf` err) $
          hPutStrLn stderr "peg-hs: the type of the start rule has no Show instance; --format cst shows the syntax tree without it"
      pure (status == ExitSuccess)

mainSource :: String -> Bool -> Maybe String -> String
mainSource moduleName withAst entry =
  unlines $
    [ "module Main (main) where"
    , ""
    , "import qualified Data.Text.IO as TIO"
    , "import qualified " <> moduleName <> " as G"
    , "import Peg.Runtime (renderParseError)"
    , "import Peg.Runtime.Syntax (debugTree)"
    , "import Pretty (pretty)"
    , "import System.Environment (getArgs)"
    , "import System.Exit (exitWith, ExitCode (..))"
    , "import System.IO (stderr)"
    , ""
    , "main :: IO ()"
    , "main = do"
    , "  args <- getArgs"
    , "  case args of"
    , "    [mode, file] -> do"
    , "      input <- TIO.readFile file"
    , "      let failed e = TIO.hPutStrLn stderr (renderParseError e) >> exitWith (ExitFailure 1)"
    , "          ast = " <> (if withAst then "either failed (putStr . pretty . show) (G.parse" <> e <> " input)" else "pure ()")
    , "          cst = either failed (TIO.putStr . debugTree G.nameOfSyntaxKind) (G.parseSyntax" <> e <> " input)"
    , "      case mode of"
    , "        \"ast\" -> ast"
    , "        \"cst\" -> cst"
    , "        _ -> putStrLn \"== AST\" >> ast >> putStrLn \"== CST\" >> cst"
    , "    _ -> exitWith (ExitFailure 2)"
    ]
  where
    e = fromMaybe "" entry
