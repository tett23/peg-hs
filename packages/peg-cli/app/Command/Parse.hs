{-# LANGUAGE OverloadedStrings #-}

-- | @peg-hs parse@: parse an input with a grammar and show its AST and CST
-- (ADR 0036). The parser generated from the grammar is compiled with GHC,
-- together with the embedded sources of peg-runtime, and the executable is
-- cached. With @--interpret@, the interpreter of peg-grammar parses the
-- input without GHC and shows the CST (ADR 0090).
module Command.Parse
  ( parseCommand
  , fnv1a
  , Ghc (..)
  , findGhc
  , cacheBase
  , compiledParser
  ) where

import Control.Monad (forM_, unless, when)
import Data.Bits (xor)
import qualified Data.ByteString as BS
import Data.Char (isSpace)
import Data.List (intercalate, isInfixOf)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Data.Version (showVersion)
import Data.Word (Word64)
import Diagnostics (reportErrors)
import Embedded (prettySource, runtimeSources)
import FileIO (readUtf8, reportFileError)
import GhcVersion (supportedGhc, supportedGhcText)
import Numeric (showHex)
import Options
import Paths_peg_cli (version)
import Peg.Codegen (Options (..), generate)
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Interpret (interpret, interpreter, interpreterKindName)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Imports (Loaded (..), loadGrammar)
import System.Directory
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import System.IO (hPutStrLn, stderr, stdout)
import Peg.Runtime (renderParseError)
import Peg.Runtime.Syntax (debugTree)
import qualified Pretty
import ProcessBytes (readProcessBytes)
import WorkDir (withWorkDir)

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
        , "packages of a project. Grammars with %env are not supported without --interpret, nor"
        , "grammars with two rules whose syntax tree types have the same name, such as expr and"
        , "Expr. Files are read as UTF-8."
        , ""
        , "With --interpret, the input is parsed without compiling, by interpreting the grammar, and"
        , "the CST is shown as with --format cst; ghc is not needed. The interpreter does not run"
        , "the actions, so it shows no AST. It evaluates predicates and the arguments of rules that"
        , "predicates read only of these forms: True, False, or a comparison (==, /=, <, <=, >, >=)"
        , "of two terms, a term being an atom, atom + atom or atom - atom, and an atom a decimal"
        , "integer, a parameter of type Int or _col. It accepts grammars with %env whose predicates"
        , "do not read _env."
        ]
    , cmdOptions =
        [ Opt "format" Nothing (Just "ast|cst|all") "what to show (default: ast, or cst with --interpret)"
        , Opt "entry" Nothing (Just "RULE") "parse with a rule of %entry instead of the start rule"
        , Opt "ghc-arg" Nothing (Just "ARG") "pass ARG to ghc, such as -isrc (repeatable)"
        , Opt "interpret" Nothing Nothing "parse by interpreting the grammar, without ghc, and show the CST"
        ]
    , cmdExamples =
        [ ("peg-hs parse Expr.hpeg input.txt", "show the value of the start rule for input.txt")
        , ("peg-hs parse --format cst Expr.hpeg input.txt", "show the lossless syntax tree")
        , ("cabal exec -- peg-hs parse --ghc-arg -isrc G.hpeg in.txt", "compile with the packages of the project and the modules under src")
        , ("peg-hs parse --interpret Expr.hpeg input.txt", "show the lossless syntax tree without compiling")
        ]
    , cmdRun = run
    }

data Format = Ast | Cst | All
  deriving (Eq)

run :: Parsed -> IO ExitCode
run p = case (parsedArguments p, value "format" p) of
  ([grammarFile, input], fmt)
    | flag "interpret" p -> case fmt of
        _ | not (null [() | ("ghc-arg", _) <- parsedOptions p]) -> commandUsageError "parse" "--interpret does not compile, so it takes no --ghc-arg"
        Just f | f `elem` ["ast", "all"] -> commandUsageError "parse" "--interpret shows only the CST: the AST is the value of the actions, which the interpreter does not run; leave out --interpret to show it"
        Just f | f /= "cst" -> commandUsageError "parse" "--format takes ast, cst or all"
        _ -> interpretFile grammarFile input (value "entry" p)
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
  loadGrammar grammarFile src >>= \loaded -> case loaded >>= \l -> let g0 = loadedGrammar l in either (\ds -> Left (grammarImports g0, templateNotes g0 ds)) (const (Right l)) (expandTemplates g0 >>= check) of
    Left (imports, diags) -> reportErrors grammarFile imports diags >> pure (ExitFailure 1)
    Right (Loaded g libraries)
      | isJust (grammarEnv g) -> failWith (grammarFile <> ": peg-hs parse does not support grammars with %env")
      | Just e <- entry, T.pack e `notElem` map unLoc (grammarEntries g) -> failWith (grammarFile <> ": " <> e <> " is not a rule of %entry")
      | otherwise ->
          findGhc "parse" >>= \case
            Left msg -> failWith msg
            Right ghc -> do
              base <- cacheBase
              compiledParser ghc base grammarFile g src libraries (format /= Cst) entry ghcArgs >>= \case
                Nothing -> pure (ExitFailure 1)
                Just exe -> do
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

-- Parse with the interpreter (ADR 0090). The output is that of the
-- compiled parser with --format cst.
interpretFile :: FilePath -> FilePath -> Maybe String -> IO ExitCode
interpretFile grammarFile input entry =
  readUtf8 directoryHint grammarFile >>= \case
    Left e -> reportFileError e >> pure (ExitFailure 1)
    Right src ->
      readUtf8 directoryHint input >>= \case
        Left e -> reportFileError e >> pure (ExitFailure 1)
        Right text -> loadGrammar grammarFile src >>= \loaded -> case loaded >>= \l -> let g0 = loadedGrammar l in either (\ds -> Left (grammarImports g0, templateNotes g0 ds)) (\(g, an) -> Right (g0, g, an)) (expandTemplates g0 >>= \g -> (,) g <$> check g) of
          Left (imports, diags) -> reportErrors grammarFile imports diags >> pure (ExitFailure 1)
          Right (g0, g, an)
            | Just e <- entry, T.pack e `notElem` map unLoc (grammarEntries g) -> failWith (grammarFile <> ": " <> e <> " is not a rule of %entry")
            | otherwise -> case interpreter g an of
                Left diags -> do
                  reportErrors grammarFile (grammarImports g0) (templateNotes g0 diags)
                  failWith "the interpreter cannot parse with this grammar; leave out --interpret to compile the parser with ghc"
                Right ip -> case interpret ip (T.pack <$> entry) text of
                  Left err -> TIO.hPutStrLn stderr (renderParseError err) >> pure (ExitFailure 1)
                  Right tree -> putStr (Pretty.readable (T.unpack (debugTree (interpreterKindName ip) tree))) >> pure ExitSuccess
  where
    directoryHint = "peg-hs parse takes a grammar file and an input file, not a directory"
    failWith msg = hPutStrLn stderr ("peg-hs: " <> msg) >> pure (ExitFailure 1)

-- | A ghc that peg-runtime supports: the program to run and its version.
data Ghc = Ghc
  { ghcProgram :: FilePath
  , ghcVersion :: String
  }

-- | The ghc on PATH, or why it cannot compile a parser, for the command of
-- the name given: there is none, or its version is not supported.
findGhc :: String -> IO (Either String Ghc)
findGhc command =
  findExecutable "ghc" >>= \case
    Nothing -> pure (Left ("peg-hs " <> command <> " needs ghc on PATH"))
    Just _ -> do
      (_, out, _) <- readProcessBytes "ghc" ["--numeric-version"]
      let v = takeWhile (not . isSpace) (T.unpack (TE.decodeUtf8Lenient out))
      pure $
        if supportedGhc v
          then Right (Ghc "ghc" v)
          else Left ("peg-hs " <> command <> " needs " <> supportedGhcText <> ", the versions peg-runtime supports; ghc is " <> v)

-- | The directory of the cache of compiled parsers:
-- @$XDG_CACHE_HOME/peg-hs/parse@, or @~/.cache/peg-hs/parse@.
cacheBase :: IO FilePath
cacheBase = do
  base <- lookupEnv "XDG_CACHE_HOME" >>= \case
    Just d | not (null d) -> pure d
    _ -> (</> ".cache") <$> getHomeDirectory
  pure (base </> "peg-hs" </> "parse")

-- | The executable of the parser of a checked grammar, from the cache under
-- the directory given, or compiled now with @ghc@ and kept in the cache.
-- It takes the mode (@ast@, @cst@ or @all@) and the input file, writes
-- what it shows to standard output and the parse error to standard error,
-- and exits with 1 on a parse error. Nothing after reporting the errors of
-- the build. An executable without the AST needs no Show instance.
--
-- The grammar is given with its text and the texts of the libraries it
-- imports, by the paths of the @%import@s (ADR 0092), which are all in
-- the key of the cache: a change of a library builds the parser again.
compiledParser :: Ghc -> FilePath -> FilePath -> Grammar -> T.Text -> [(FilePath, T.Text)] -> Bool -> Maybe String -> [String] -> IO (Maybe FilePath)
compiledParser ghc base grammarFile g src libraries withAst entry ghcArgs = do
  let dir = cacheDir base (T.unpack src) libraries entry ghcArgs (ghcVersion ghc)
      exe = parserPath dir withAst
  built <- doesFileExist exe
  ok <-
    if built
      then pure True
      else build ghc grammarFile g dir withAst entry ghcArgs
  pure (if ok then Just exe else Nothing)

-- The cache directory for a grammar, its libraries in the order of the
-- @%import@s, the options and the versions.
cacheDir :: FilePath -> String -> [(FilePath, T.Text)] -> Maybe String -> [String] -> String -> FilePath
cacheDir base src libraries entry ghcArgs v =
  let key = intercalate "\0" [src, intercalate "\1" [p <> "\2" <> T.unpack t | (p, t) <- libraries], fromMaybe "" entry, intercalate "\1" ghcArgs, showVersion version, v, mainVersion]
   in base </> fnv1a key

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

-- Write the sources to a working directory of its own (ADR 0077) and
-- compile them into the cache; report GHC's errors. The working directory
-- is removed in any case.
build :: Ghc -> FilePath -> Grammar -> FilePath -> Bool -> Maybe String -> [String] -> IO Bool
build ghc grammarFile g dir withAst entry ghcArgs = withWorkDir $ \work -> do
  let srcDir = work </> "src"
      moduleName = T.unpack (unLoc (grammarModule g))
      modulePath = srcDir </> map (\c -> if c == '.' then '/' else c) moduleName <> ".hs"
      syntaxGrammar = g {grammarSyntax = Just (fromMaybe (Loc 0 1 1) (grammarSyntax g))}
      opts = Options {optSourceName = grammarFile, optOutputName = modulePath, optDebugEntry = False, optExports = Nothing}
  case generate opts syntaxGrammar of
    Left diags -> reportErrors grammarFile (grammarImports g) diags >> pure False
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
        readProcessBytes (ghcProgram ghc) (["--make", "-O0", "-v0", "-i" <> srcDir, "-outputdir", work </> "build", "-o", work </> "parser", srcDir </> "Main.hs"] ++ ghcArgs)
      -- Another peg-hs may be building the same parser: the executable
      -- appears in the cache at once, by a rename.
      when (status == ExitSuccess) $ renameFile (work </> "parser") exe
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
