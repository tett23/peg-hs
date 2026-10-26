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
import Data.List (intercalate, isInfixOf)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Version (showVersion)
import Data.Word (Word64)
import Diagnostics (reportErrors)
import Embedded (prettySource, runtimeSources)
import FileIO (readUtf8, reportFileError)
import GhcVersion (supportedGhc, supportedGhcText)
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
import System.IO (hPutStrLn, stderr, stdout)
import ProcessBytes (readProcessBytes)

parseCommand :: Command
parseCommand =
  Command
    { cmdName = "parse"
    , cmdSummary = "parse an input with a grammar and show its AST and CST"
    , cmdArguments = "GRAMMAR.hpeg INPUT"
    , cmdDescription =
        [ "Parse INPUT with the grammar and show the value of the start rule (the AST)"
        , "or the lossless syntax tree (the CST). The parser is compiled with the ghc on PATH"
        , "(GHC 9.10, 9.12 or 9.14), and cached under $XDG_CACHE_HOME/peg-hs/parse. The AST needs"
        , "a Show instance of the type of the start rule. Run through cabal exec to use the"
        , "packages of a project. Grammars with %env are not supported, nor grammars with two rules"
        , "whose syntax tree types have the same name, such as expr and Expr. Files are read as UTF-8."
        ]
    , cmdOptions =
        [ Opt "format" Nothing (Just "ast|cst|all") "what to show (default: ast)"
        , Opt "entry" Nothing (Just "RULE") "parse with a rule of %entry instead of the start rule"
        , Opt "ghc-arg" Nothing (Just "ARG") "pass ARG to ghc, such as -isrc (repeatable)"
        ]
    , cmdExamples =
        [ ("peg-hs parse Expr.hpeg input.txt", "show the value of the start rule for input.txt")
        , ("peg-hs parse --format cst Expr.hpeg input.txt", "show the lossless syntax tree")
        , ("cabal exec -- peg-hs parse --ghc-arg -isrc G.hpeg in.txt", "compile with the packages of the project and the modules under src")
        ]
    , cmdRun = run
    }

data Format = Ast | Cst | All
  deriving (Eq)

run :: Parsed -> IO ExitCode
run p = case (parsedArguments p, value "format" p) of
  ([grammarFile, input], fmt)
    | Just format <- maybe (Just Ast) formatOf fmt -> parseWith grammarFile input format (value "entry" p) [v | ("ghc-arg", v) <- parsedOptions p]
    | otherwise -> commandUsageError "parse" "--format takes ast, cst or all"
  ([_], _) -> commandUsageError "parse" "parse needs a grammar file and an input file"
  ([], _) -> commandUsageError "parse" "parse needs a grammar file and an input file"
  _ -> commandUsageError "parse" "parse takes a grammar file and an input file"
  where
    formatOf = \case
      "ast" -> Just Ast
      "cst" -> Just Cst
      "all" -> Just All
      _ -> Nothing

parseWith :: FilePath -> FilePath -> Format -> Maybe String -> [String] -> IO ExitCode
parseWith grammarFile input format entry ghcArgs =
  readUtf8 directoryHint grammarFile >>= \case
    Left e -> reportFileError e >> pure (ExitFailure 1)
    Right src ->
      -- The input is read here too, to report a file that cannot be read
      -- before compiling.
      readUtf8 directoryHint input >>= \case
        Left e -> reportFileError e >> pure (ExitFailure 1)
        Right _ -> parseText grammarFile input format entry ghcArgs src
  where
    directoryHint = "peg-hs parse takes a grammar file and an input file, not a directory"

parseText :: FilePath -> FilePath -> Format -> Maybe String -> [String] -> T.Text -> IO ExitCode
parseText grammarFile input format entry ghcArgs src =
  case parseGrammar src >>= \g0 -> either (Left . templateNotes g0) (const (Right g0)) (expandTemplates g0 >>= check) of
    Left diags -> reportErrors grammarFile diags >> pure (ExitFailure 1)
    Right g
      | isJust (grammarEnv g) -> failWith (grammarFile <> ": peg-hs parse does not support grammars with %env")
      | Just e <- entry, T.pack e `notElem` map unLoc (grammarEntries g) -> failWith (grammarFile <> ": " <> e <> " is not a rule of %entry")
      | otherwise ->
          findExecutable "ghc" >>= \case
            Nothing -> failWith "peg-hs parse needs ghc on PATH"
            Just _ -> do
              (_, out, _) <- readProcessBytes "ghc" ["--numeric-version"]
              let ghcVersion = takeWhile (not . isSpace) (T.unpack (TE.decodeUtf8Lenient out))
              if not (supportedGhc ghcVersion)
                then failWith ("peg-hs parse needs " <> supportedGhcText <> ", the versions peg-runtime supports; ghc is " <> ghcVersion)
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
                      (code, out', err) <- readProcessBytes exe [modeArg format, input]
                      BS.hPut stdout out'
                      BS.hPut stderr err
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
  let key = intercalate "\0" [src, fromMaybe "" entry, intercalate "\1" ghcArgs, showVersion version, ghcVersion, mainVersion]
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
      opts = Options {optSourceName = grammarFile, optOutputName = modulePath, optDebugEntry = False, optExports = Nothing}
  case generate opts syntaxGrammar of
    Left diags -> reportErrors grammarFile diags >> pure False
    Right code -> do
      createDirectoryIfMissing True (takeDirectory modulePath)
      BS.writeFile modulePath (TE.encodeUtf8 code)
      forM_ runtimeSources $ \(path, text) -> do
        createDirectoryIfMissing True (takeDirectory (srcDir </> path))
        writeUtf8String (srcDir </> path) text
      writeUtf8String (srcDir </> "Pretty.hs") prettySource
      writeUtf8String (srcDir </> "Main.hs") (mainSource moduleName withAst entry)
      createDirectoryIfMissing True dir
      let exe = parserPath dir withAst
      (status, out, err) <-
        readProcessBytes "ghc" (["--make", "-O0", "-v0", "-i" <> srcDir, "-outputdir", work </> "build", "-o", work </> "parser", srcDir </> "Main.hs"] ++ ghcArgs)
      -- Another peg-hs may be building the same parser: the executable
      -- appears in the cache at once, by a rename.
      when (status == ExitSuccess) $ renameFile (work </> "parser") exe
      removeDirectoryRecursive work
      unless (status == ExitSuccess) $ do
        BS.hPut stderr (out <> err)
        let errText = T.unpack (TE.decodeUtf8Lenient err)
        when (withAst && "Show" `isInfixOf` errText && "No instance" `isInfixOf` errText) $
          hPutStrLn stderr "peg-hs: the type of the start rule has no Show instance; --format cst shows the syntax tree without it"
      pure (status == ExitSuccess)

-- Write a source file as UTF-8, whatever the locale.
writeUtf8String :: FilePath -> String -> IO ()
writeUtf8String path = BS.writeFile path . TE.encodeUtf8 . T.pack

-- The version of the main module below, in the key of the cache: a parser
-- built with an older main module is built again.
mainVersion :: String
mainVersion = "2"

-- The main module of the parser. It reads the input as UTF-8 without a byte
-- order mark, and writes UTF-8, whatever the locale (ADR 0045).
mainSource :: String -> Bool -> Maybe String -> String
mainSource moduleName withAst entry =
  unlines $
    [ "module Main (main) where"
    , ""
    , "import qualified Data.ByteString as BS"
    , "import qualified Data.Text as T"
    , "import qualified Data.Text.Encoding as TE"
    , "import qualified Data.Text.IO as TIO"
    , "import qualified " <> moduleName <> " as G"
    , "import Peg.Runtime (renderParseError)"
    , "import Peg.Runtime.Syntax (debugTree)"
    , "import Pretty (pretty, readable)"
    , "import System.Environment (getArgs)"
    , "import System.Exit (exitWith, ExitCode (..))"
    , "import System.IO (hSetEncoding, mkTextEncoding, stderr, stdout)"
    , ""
    , "main :: IO ()"
    , "main = do"
    , "  enc <- mkTextEncoding \"UTF-8//ROUNDTRIP\""
    , "  hSetEncoding stdout enc"
    , "  hSetEncoding stderr enc"
    , "  args <- getArgs"
    , "  case args of"
    , "    [mode, file] -> do"
    , "      bytes <- BS.readFile file"
    , "      let input = TE.decodeUtf8 (if BS.pack [0xEF, 0xBB, 0xBF] `BS.isPrefixOf` bytes then BS.drop 3 bytes else bytes)"
    , "      let failed e = TIO.hPutStrLn stderr (renderParseError e) >> exitWith (ExitFailure 1)"
    , "          ast = " <> (if withAst then "either failed (putStr . pretty . readable . show) (G.parse" <> e <> " input)" else "pure ()")
    , "          cst = either failed (putStr . readable . T.unpack . debugTree G.nameOfSyntaxKind) (G.parseSyntax" <> e <> " input)"
    , "      case mode of"
    , "        \"ast\" -> ast"
    , "        \"cst\" -> cst"
    , "        _ -> putStrLn \"== AST\" >> ast >> putStrLn \"== CST\" >> cst"
    , "    _ -> exitWith (ExitFailure 2)"
    ]
  where
    e = fromMaybe "" entry
