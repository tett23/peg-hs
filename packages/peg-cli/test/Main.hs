-- | Tests of the peg-hs executable: the commands (ADR 0037), and the
-- warnings, --Werror and --strip-labels of gen (ADR 0028).
module Main (main) where

import Control.Monad (forM, when)
import qualified Data.ByteString.Char8 as BC
import Data.Char (isDigit)
import Data.List (nub, sort)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Grammar (Diagnostic (..), Loc (..))
import Peg.Lsp.Server (Severity (..), diagnose)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeExtension)
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.List (isInfixOf, isPrefixOf)
import System.Directory (createDirectoryIfMissing, doesFileExist, getTemporaryDirectory, removeDirectoryRecursive, removeFile)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, takeFileName, (</>))
import System.Process (proc, readCreateProcessWithExitCode, readProcessWithExitCode)
import System.Environment (getEnvironment)
import System.Directory (findExecutable, getPermissions, removePathForcibly, setOwnerExecutable, setPermissions)
import Data.Char (isSpace)
import Embedded (prettySource, runtimeSources)
import Pretty (pretty, readable)
import Test.Tasty.QuickCheck
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import qualified Data.ByteString as BS
import qualified Data.Text.Encoding as TE
import Data.Either (isRight)
import Control.Monad (forM_, unless)
import Control.Exception (bracket_)
import qualified Control.Exception
import System.IO (hClose, hSetBinaryMode)
import System.Process (CreateProcess (..), StdStream (..), createProcess, waitForProcess)
import System.Directory (emptyPermissions)
import FileIO (utf8ErrorOffset, decodeUtf8File)
import GhcVersion (supportedGhc)
import EditDistance (editDistance)

unsafe :: String
unsafe = "%module M\nS :: ()\nS <- 'a' ('b' ^l) { () } / 'a' 'c' { () }\n"

-- Run peg-hs with arguments.
pegHs :: [String] -> IO (ExitCode, String, String)
pegHs args = readProcessWithExitCode "peg-hs" args ""

-- Run peg-hs gen on a grammar written to a fresh file.
genOn :: String -> String -> [String] -> IO (ExitCode, String, String, Bool)
genOn name grammar flags = do
  dir <- testDir
  let input = dir </> (name <> ".peg")
      output = dir </> (name <> ".hs")
  doesFileExist output >>= \e -> when e (removeFile output)
  writeFile input grammar
  (code, out, err) <- pegHs (["gen", input, "-o", output] ++ flags)
  written <- doesFileExist output
  pure (code, out, err, written)

testDir :: IO FilePath
testDir = do
  tmp <- getTemporaryDirectory
  let dir = tmp </> "peg-cli-test"
  createDirectoryIfMissing True dir
  pure dir

unformatted, formatted :: String
unformatted = "%module M\nS::()\nS<-'a'   {()}\n   /'b' { () }\n"
formatted = "%module M\n\nS :: ()\nS <- 'a' { () }\n  / 'b' { () }\n"

exprGrammar :: String
exprGrammar =
  unlines
    [ "%module Example.Expr"
    , "%entry Term"
    , "%{"
    , "import qualified Data.Text as T"
    , ""
    , "data Expr = Num Int | Add Expr Expr"
    , "  deriving (Show)"
    , "}%"
    , ""
    , "Expr :: Expr"
    , "Expr <- l:Expr Sp '+' Sp r:Term { Add l r }"
    , "     / Term"
    , ""
    , "Term :: Expr"
    , "Term <- d:$[0-9]+ { Num (T.length d) }"
    , ""
    , "Sp :: ()"
    , "Sp <- ' '* { () }"
    ]

replace :: String -> String -> String -> String
replace old new = T.unpack . T.replace (T.pack old) (T.pack new) . T.pack

-- A directory with a ghc that logs its calls: GHC 9.10 (ghc-9.10.3 when
-- ghc is another version), and a cache of its own.
parseEnv :: String -> IO (FilePath, [(String, String)])
parseEnv tag = do
  base <- testDir
  let cache = base </> ("parse-cache-" <> tag)
  e <- getEnvironment
  let path = (base </> "parse-bin") <> ":" <> maybe "" id (lookup "PATH" e)
  pure
    ( base
    , ("PATH", path)
        : ("XDG_CACHE_HOME", cache)
        : ("PEG_TEST_GHC_LOG", base </> ("ghc-" <> tag <> ".log"))
        : [(k, v) | (k, v) <- e, k `notElem` ["PATH", "XDG_CACHE_HOME", "PEG_TEST_GHC_LOG"]]
    )

-- The ghc of parseEnv, written once before the tests run: the tests run in
-- parallel, and on Linux a script that another thread has open for writing
-- cannot be executed (ADR 0039). It logs its calls to $PEG_TEST_GHC_LOG.
writeGhcWrapper :: IO ()
writeGhcWrapper = do
  base <- testDir
  let bin = base </> "parse-bin"
      wrapper = bin </> "ghc"
  createDirectoryIfMissing True bin
  real <- findExecutable "ghc-9.10.3" >>= maybe (maybe "ghc" id <$> findExecutable "ghc") pure
  writeFile wrapper ("#!/bin/sh\necho \"$*\" >> \"$PEG_TEST_GHC_LOG\"\nexec " <> real <> " \"$@\"\n")
  getPermissions wrapper >>= setPermissions wrapper . setOwnerExecutable True

-- The number of compilations so far by the tests of a name.
compiles :: String -> IO Int
compiles tag = do
  base <- testDir
  let file = base </> ("ghc-" <> tag <> ".log")
  exists <- doesFileExist file
  if exists then length . filter (T.isPrefixOf (T.pack "--make ")) . T.lines <$> TIO.readFile file else pure 0

parseIn :: FilePath -> [String] -> IO (ExitCode, String, String)
parseIn dir args = do
  (_, e) <- parseEnv (takeFileName dir)
  readCreateProcessWithExitCode (proc "peg-hs" args) {cwd = Just dir, env = Just e} ""

-- Run peg-hs parse on a grammar and an input in a fresh directory.
parseRun :: String -> String -> String -> [String] -> IO (ExitCode, String, String)
parseRun name grammar input flags = do
  dir <- treeWith ("parse-" <> name) [("G.peg", grammar), ("in.txt", input)]
  parseIn dir (["parse", "G.peg", "in.txt"] ++ flags)

parseOut :: String -> [String] -> IO BL.ByteString
parseOut name flags = (\(_, out, err) -> BL.pack (out <> err)) <$> parseRun name exprGrammar "1 + 22 + 333" flags

-- Long values, which do not fit in a line.
genLong :: Gen String
genLong = show <$> (vectorOf 6 ((,) <$> (arbitrary :: Gen Int) <*> listOf1 (Just <$> (arbitrary :: Gen [Int]))))

-- The column where the contents of a line start, after its indentation and
-- a leading comma.
contentColumn :: String -> Int
contentColumn l = let (sp, rest) = span (== ' ') l in length sp + (case rest of ',' : ' ' : _ -> 2; _ -> 0)

-- The brackets left open at the start of each line, less those the line
-- starts by closing. Values of genLong have no brackets inside strings.
depths :: [String] -> [Int]
depths = go 0
  where
    go _ [] = []
    go d (l : ls) =
      let closing = length (takeWhile (`elem` (")]}" :: String)) (dropWhile (== ' ') l))
          d' = d + length (filter (`elem` ("([{" :: String)) l) - length (filter (`elem` (")]}" :: String)) l)
       in (d - closing) : go d' ls

-- The show of random values with records, lists, strings and characters.
genShown :: Gen String
genShown = oneof [show <$> (arbitrary :: Gen [(Int, Maybe String)]), show <$> (arbitrary :: Gen (Either [Char] (Bool, [[Int]])))]

-- A diagnostic written by peg-hs: line, column, whether it is an error,
-- and the message.
cliDiagnostic :: FilePath -> String -> [(Int, Int, Bool, String)]
cliDiagnostic file l
  | (file <> ":") `isPrefixOf` l =
      let rest = drop (length file + 1) l
          (line, rest') = span isDigit rest
          (col, rest'') = span isDigit (drop 1 rest')
       in case (line, col, drop 2 rest'') of
            (_ : _, _ : _, r)
              | "error: " `isPrefixOf` r -> [(read line, read col, True, drop 7 r)]
              | "warning: " `isPrefixOf` r -> [(read line, read col, False, drop 9 r)]
            _ -> []
  | otherwise = []

-- The grammars of the repository; none in a source tarball.
repositoryGrammars :: IO [FilePath]
repositoryGrammars = concat <$> mapM pegsIn ["../peg-grammar/grammar", "../peg-codegen/test/fixtures", "../../conformance/json", "../../conformance/lua", "../../conformance/toml", "../../conformance/commonmark"]
  where
    pegsIn d = do
      exists <- doesDirectoryExist d
      if exists then map (d </>) . filter ((== ".peg") . takeExtension) <$> listDirectory d else pure []

-- One character deleted or duplicated, at a few positions of a file.
mutants :: T.Text -> [T.Text]
mutants src =
  concat
    [ [T.take i src <> T.drop (i + 1) src, T.take (i + 1) src <> T.drop i src]
    | i <- [step, 2 * step .. T.length src - 1]
    ]
  where
    step = max 1 (T.length src `div` 3)

-- A grammar with one warning of the linter.
linted :: String
linted = "%module M\nS :: ()\nS <- 'a'? { () } / 'b' { () }\n"

-- A fresh directory with the given files.
treeWith :: String -> [(FilePath, String)] -> IO FilePath
treeWith name files = do
  base <- testDir
  let dir = base </> name
  createDirectoryIfMissing True dir
  removeDirectoryRecursive dir
  createDirectoryIfMissing True dir
  mapM_ (\(f, c) -> createDirectoryIfMissing True (takeDirectory (dir </> f)) >> writeFile (dir </> f) c) files
  pure dir

-- Run peg-hs in a directory.
pegHsIn :: FilePath -> [String] -> IO (ExitCode, String, String)
pegHsIn dir args = readCreateProcessWithExitCode (proc "peg-hs" args) {cwd = Just dir} ""

-- The files of the discovery test: two to format, and three to skip.
discoveryTree :: [(FilePath, String)]
discoveryTree =
  [ ("A.peg", unformatted)
  , ("sub/deeper/B.peg", unformatted)
  , (".hidden/C.peg", unformatted)
  , ("dist-newstyle/D.peg", unformatted)
  , ("sub/E.txt", unformatted)
  ]

stdoutOf :: [String] -> IO BL.ByteString
stdoutOf args = (\(_, out, _) -> BL.pack out) <$> pegHs args


-- Run peg-hs in a directory with more variables of the environment, and
-- take its output as bytes, whatever the locale of the test.
pegHsBytes :: FilePath -> [(String, String)] -> [String] -> IO (ExitCode, BS.ByteString, BS.ByteString)
pegHsBytes dir extra args = do
  e <- getEnvironment
  let env' = extra ++ [(k, v) | (k, v) <- e, k `notElem` map fst extra]
  (_, Just o, Just er, ph) <- createProcess (proc "peg-hs" args) {cwd = Just dir, env = Just env', std_out = CreatePipe, std_err = CreatePipe}
  hSetBinaryMode o True
  hSetBinaryMode er True
  out <- BS.hGetContents o
  err <- BS.hGetContents er
  code <- waitForProcess ph
  hClose o >> hClose er
  pure (code, out, err)

-- The C locale, where GHC's default encoding is ASCII.
cLocale :: [(String, String)]
cLocale = [("LANG", "C"), ("LC_ALL", "C"), ("LC_CTYPE", "C")]

-- A grammar in Japanese: a comment, a character class and a literal.
japaneseGrammar :: String
japaneseGrammar = "%module M\n\n# ひらがなの並び\nS :: ()\nS <- [あ-ん]+ '。' { () }\n"

-- The standard error of peg-hs in a directory, with the directory in place
-- of the current directory, for the golden test of the errors.
errorsIn :: FilePath -> [String] -> IO String
errorsIn dir args = do
  (code, _, err) <- pegHsIn dir args
  pure ("$ peg-hs " <> unwords args <> "\n" <> withoutDir dir err <> "exit: " <> show code <> "\n\n")

-- Bytes that are often UTF-8 and often not.
genBytes :: Gen BS.ByteString
genBytes =
  BS.concat
    <$> listOf
      ( oneof
          [ TE.encodeUtf8 . T.pack <$> (arbitrary :: Gen String)
          , BS.pack <$> listOf (elements ([0x00, 0x41, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1, 0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xFF]))
          ]
      )

main :: IO ()
main = do
  writeGhcWrapper
  defaultMain $
    testGroup
      "peg-hs"
      [ testGroup
          "commands (ADR 0037)"
          [ goldenVsString "peg-hs help" "test/golden/help.txt" (stdoutOf ["help"])
          , goldenVsString "peg-hs, on stderr" "test/golden/no-command.txt" ((\(_, _, err) -> BL.pack err) <$> pegHs [])
          , goldenVsString "peg-hs help gen" "test/golden/help-gen.txt" (stdoutOf ["help", "gen"])
          , testCase "peg-hs gen --help is peg-hs help gen" $ do
              a <- stdoutOf ["gen", "--help"]
              b <- stdoutOf ["help", "gen"]
              a @?= b
          , testCase "no command is a usage error" $ do
              (code, out, err) <- pegHs []
              code @?= ExitFailure 2
              out @?= ""
              assertBool err ("commands:" `isInfixOf` err)
          , testCase "an unknown command is a usage error" $ do
              (code, _, err) <- pegHs ["frobnicate"]
              code @?= ExitFailure 2
              assertBool err ("unknown command frobnicate" `isInfixOf` err)
          , testCase "a grammar without a command points to gen" $ do
              (code, _, err) <- pegHs ["Grammar.peg"]
              code @?= ExitFailure 2
              assertBool err ("peg-hs gen Grammar.peg" `isInfixOf` err)
          , testCase "an unknown option is a usage error" $ do
              (code, _, err) <- pegHs ["gen", "--frobnicate", "x.peg"]
              code @?= ExitFailure 2
              assertBool err ("unknown option --frobnicate" `isInfixOf` err)
          , testCase "usage errors of lsp, parse and fmt" $ do
              codes <- mapM (fmap (\(c, _, _) -> c) . pegHs) [["lsp", "x"], ["parse", "G.peg"], ["parse", "--format", "xml", "G.peg", "in.txt"], ["fmt", "--frobnicate"], ["lint", "--frobnicate"]]
              codes @?= replicate 5 (ExitFailure 2)
          , testCase "a missing argument is a usage error" $ do
              (code, _, _) <- pegHs ["gen"]
              code @?= ExitFailure 2
          , testCase "--version" $ do
              (code, out, _) <- pegHs ["--version"]
              code @?= ExitSuccess
              assertBool out ("peg-hs 0.1" `isInfixOf` out)
          , testCase "an error in the grammar fails with 1, on stderr" $ do
              (code, out, err, written) <- genOn "broken" "%module M\nS :: ()\nS <- Missing { () }\n" []
              code @?= ExitFailure 1
              out @?= ""
              assertBool err ("error: undefined rule Missing" `isInfixOf` err)
              assertBool "no module is written" (not written)
          , testCase "the report of the written module is on stdout" $ do
              (code, out, err, _) <- genOn "ok" "%module M\nS :: ()\nS <- 'a' { () }\n" []
              code @?= ExitSuccess
              assertBool out ("wrote " `isInfixOf` out)
              err @?= ""
          ]
      , testGroup
          "the details of the command line (ADR 0046)"
          [ goldenVsString "peg-hs help parse" "test/golden/help-parse.txt" (stdoutOf ["help", "parse"])
          , goldenVsString "peg-hs help lsp" "test/golden/help-lsp.txt" (stdoutOf ["help", "lsp"])
          , testCase "the help lists --version and --help" $ do
              out <- BL.unpack <$> stdoutOf ["help"]
              assertBool out ("--version" `isInfixOf` out && "--help" `isInfixOf` out)
          , testCase "the help of every command has its options and examples" $
              forM_ ["gen", "fmt", "lint", "lsp", "parse"] $ \c -> do
                out <- BL.unpack <$> stdoutOf ["help", c]
                assertBool out (all (`elem` lines out) ["options:", "examples:"])
                assertBool out ("-h, --help" `isInfixOf` out)
          , testCase "--name=value is --name value" $ do
              dir <- treeWith "cli-equals" [("G.peg", exprGrammar), ("in.txt", "1 + 2")]
              (code, _, err) <- pegHsIn dir ["gen", "--output=Out.hs", "G.peg"]
              (code, err) @?= (ExitSuccess, "")
              doesFileExist (dir </> "Out.hs") >>= assertBool "Out.hs"
              (code', out', _) <- parseIn dir ["parse", "G.peg", "in.txt", "--format=cst", "--entry=Term", "--ghc-arg=-O0"]
              (code'', out'', _) <- parseIn dir ["parse", "G.peg", "in.txt", "--format", "cst", "--entry", "Term", "--ghc-arg", "-O0"]
              (code', out') @?= (code'', out'')
          , testCase "a value given to an option without one is a usage error" $ do
              (code, _, err) <- pegHs ["gen", "--debug-entry=x", "G.peg"]
              code @?= ExitFailure 2
              assertBool err ("the option --debug-entry takes no value" `isInfixOf` err)
          , testCase "a usage error points to the help of the command" $ do
              (code, out, err) <- pegHs ["gen"]
              (code, out) @?= (ExitFailure 2, "")
              lines err @?= ["peg-hs: gen needs a grammar file", "Run peg-hs help gen for its usage."]
              (_, _, err') <- pegHs ["parse", "--frobnicate"]
              lines err' @?= ["peg-hs: unknown option --frobnicate", "Run peg-hs help parse for its usage."]
          , testCase "an unknown command near a command suggests it" $ do
              (code, out, err) <- pegHs ["fnt"]
              (code, out) @?= (ExitFailure 2, "")
              lines err @?= ["peg-hs: unknown command fnt", "Did you mean fmt?", "Run peg-hs help for the commands."]
              (_, _, err') <- pegHs ["help", "prase"]
              lines err' @?= ["peg-hs: unknown command prase", "Did you mean parse?", "Run peg-hs help for the commands."]
          , testCase "an unknown command far from every command suggests nothing" $ do
              (_, _, err) <- pegHs ["xyzzy"]
              lines err @?= ["peg-hs: unknown command xyzzy", "Run peg-hs help for the commands."]
          , testCase "the edit distance" $
              map (uncurry editDistance) [("fmt", "fnt"), ("parse", "prase"), ("", "abc"), ("lint", "lint"), ("gen", "xyzzy")] @?= [1, 2, 3, 0, 5]
          ]
      , testGroup
          "fmt (ADR 0032)"
          [ goldenVsString "peg-hs help fmt" "test/golden/help-fmt.txt" (stdoutOf ["help", "fmt"])
          , testCase "fmt formats a file in place" $ do
              dir <- treeWith "fmt-one" [("G.peg", unformatted)]
              (code, out, err) <- pegHsIn dir ["fmt", "G.peg"]
              (code, out, err) @?= (ExitSuccess, "", "")
              readFile (dir </> "G.peg") >>= (@?= formatted)
          , testCase "--check succeeds on a formatted file" $ do
              dir <- treeWith "fmt-ok" [("G.peg", formatted)]
              (code, out, _) <- pegHsIn dir ["fmt", "--check", "G.peg"]
              (code, out) @?= (ExitSuccess, "")
          , testCase "--check fails on an unformatted file, names it and writes nothing" $ do
              dir <- treeWith "fmt-ng" [("G.peg", unformatted)]
              (code, out, _) <- pegHsIn dir ["fmt", "--check", "G.peg"]
              (code, out) @?= (ExitFailure 1, "G.peg\n")
              readFile (dir </> "G.peg") >>= (@?= unformatted)
          , testCase "a file with a syntax error is reported, and the others are formatted" $ do
              dir <- treeWith "fmt-broken" [("A.peg", "%module M\nS <- 'a\n"), ("B.peg", unformatted)]
              (code, _, err) <- pegHsIn dir ["fmt", "A.peg", "B.peg"]
              code @?= ExitFailure 1
              assertBool err ("A.peg:2:8: error: unterminated literal" `isInfixOf` err)
              readFile (dir </> "B.peg") >>= (@?= formatted)
          , testCase "--check without files walks the directory" $ do
              dir <- treeWith "fmt-walk-check" discoveryTree
              (code, out, _) <- pegHsIn dir ["fmt", "--check"]
              (code, out) @?= (ExitFailure 1, "A.peg\nsub/deeper/B.peg\n")
          , testCase "fmt without files formats the files of the directory" $ do
              dir <- treeWith "fmt-walk" discoveryTree
              (code, _, _) <- pegHsIn dir ["fmt"]
              code @?= ExitSuccess
              contents <- mapM (readFile . (dir </>) . fst) discoveryTree
              contents @?= [formatted, formatted, unformatted, unformatted, unformatted]
          ]
      , testGroup
          "lint (ADR 0033)"
          [ goldenVsString "peg-hs help lint" "test/golden/help-lint.txt" (stdoutOf ["help", "lint"])
          , testCase "a grammar without warnings succeeds" $ do
              dir <- treeWith "lint-ok" [("G.peg", formatted)]
              (code, out, err) <- pegHsIn dir ["lint", "G.peg"]
              (code, out, err) @?= (ExitSuccess, "", "")
          , testCase "a warning fails with 1, on stderr" $ do
              dir <- treeWith "lint-ng" [("G.peg", linted)]
              (code, out, err) <- pegHsIn dir ["lint", "G.peg"]
              (code, out) @?= (ExitFailure 1, "")
              err @?= "G.peg:3:20: warning: the alternative is never tried: the alternative at 3:6 always succeeds [unreachable-alternative]; remove it, or move it before the one that always succeeds\n"
          , testCase "an error in the grammar fails with 1" $ do
              dir <- treeWith "lint-broken" [("G.peg", "%module M\nS :: ()\nS <- Missing { () }\n")]
              (code, _, err) <- pegHsIn dir ["lint", "G.peg"]
              code @?= ExitFailure 1
              assertBool err ("G.peg:3:6: error: undefined rule Missing" `isInfixOf` err)
          , testCase "without files, lint the files fmt formats" $ do
              dir <- treeWith "lint-walk" [(f, linted) | (f, _) <- discoveryTree]
              (code, _, err) <- pegHsIn dir ["lint"]
              code @?= ExitFailure 1
              map (takeWhile (/= ':')) (lines err) @?= ["A.peg", "sub/deeper/B.peg"]
          ]
      , testGroup
          "lsp (ADR 0035)"
          [ testCase "a session with the process on standard input and output" $ do
              let frame body = "Content-Length: " <> show (length (BC.unpack (BC.pack body))) <> "\r\n\r\n" <> body
                  msgs =
                    [ "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{}}}"
                    , "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}"
                    , "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///g.peg\",\"languageId\":\"peg\",\"version\":1,\"text\":\"%module M\\nS :: ()\\nS <- Missing { () }\\n\"}}}"
                    , "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"shutdown\"}"
                    , "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}"
                    ]
              (code, out, _) <- readProcessWithExitCode "peg-hs" ["lsp"] (concatMap frame msgs)
              code @?= ExitSuccess
              assertBool out ("\"id\":1,\"result\":{\"capabilities\"" `isInfixOf` out)
              assertBool out ("undefined rule Missing" `isInfixOf` out)
              assertBool out ("\"id\":2,\"result\":null" `isInfixOf` out)
          , testCase "exit without shutdown fails" $ do
              (code, _, _) <- readProcessWithExitCode "peg-hs" ["lsp"] "Content-Length: 33\r\n\r\n{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}"
              code @?= ExitFailure 1
          , testCase "the diagnostics are those of peg-hs gen and peg-hs lint" $ do
              files <- repositoryGrammars
              dir <- treeWith "lsp-agree" []
              bad <- fmap concat . forM files $ \f -> do
                src <- TIO.readFile f
                fmap concat . forM (zip [0 :: Int ..] (src : take 3 (mutants src))) $ \(k, m) -> do
                  let file = dir </> (show k <> "-" <> takeFileName f)
                  TIO.writeFile file m
                  (_, _, genErr) <- pegHs ["gen", file, "-o", dir </> "out.hs"]
                  (_, _, lintErr) <- pegHs ["lint", file]
                  let cli = nub (sort (concatMap (cliDiagnostic file) (lines genErr ++ lines lintErr)))
                      lsp = [(locLine l, locColumn l, sev == Error, T.unpack msg) | (sev, Diagnostic l msg, _) <- diagnose m]
                      syntaxError = case cli of
                        [(_, _, True, _)] -> True
                        _ -> False
                      agree = if syntaxError && not (null lsp) then take 1 lsp == cli else sort lsp == cli
                  pure [(file, cli, lsp) | not agree]
              take 1 bad @?= []
          ]
      , testGroup
          "parse (ADR 0036)"
          [ goldenVsString "the AST by default" "test/golden/parse-ast.txt" (parseOut "ast" [])
          , goldenVsString "--format cst, of a grammar without %syntax" "test/golden/parse-cst.txt" (parseOut "cst" ["--format", "cst"])
          , goldenVsString "--format all" "test/golden/parse-all.txt" (parseOut "all" ["--format", "all"])
          , testCase "--entry parses with a rule of %entry" $ do
              (code, out, _) <- parseRun "entry" exprGrammar "22" ["--entry", "Term"]
              (code, out) @?= (ExitSuccess, "Num 2\n")
          , testCase "--entry of a rule not in %entry is an error" $ do
              (code, _, err) <- parseRun "entry-bad" exprGrammar "22" ["--entry", "Expr"]
              code @?= ExitFailure 1
              assertBool err ("Expr is not a rule of %entry" `isInfixOf` err)
          , testCase "an input the grammar rejects fails with the parse error" $ do
              (code, out, err) <- parseRun "reject" exprGrammar "1 +" []
              (code, out, err) @?= (ExitFailure 1, "", "1:4: expected ' ' or [0-9]\n")
          , testCase "without a Show instance, the error points to --format cst" $ do
              (code, _, err) <- parseRun "noshow" (filter (/= '\r') (replace "  deriving (Show)\n" "" exprGrammar)) "1" []
              code @?= ExitFailure 1
              assertBool err ("--format cst shows the syntax tree" `isInfixOf` err)
              (code', out', _) <- parseRun "noshow" (replace "  deriving (Show)\n" "" exprGrammar) "1" ["--format", "cst"]
              (code', take 5 out') @?= (ExitSuccess, "Expr@")
          , testCase "without ghc on PATH, an error" $ do
              dir <- treeWith "parse-noghc" [("G.peg", exprGrammar), ("in.txt", "1")]
              Just exe <- findExecutable "peg-hs"
              e <- getEnvironment
              (code, _, err) <- readCreateProcessWithExitCode (proc exe ["parse", "G.peg", "in.txt"]) {cwd = Just dir, env = Just (("PATH", dir) : [(k, v) | (k, v) <- e, k /= "PATH"])} ""
              (code, err) @?= (ExitFailure 1, "peg-hs: peg-hs parse needs ghc on PATH\n")
          , testCase "a grammar with %env is an error" $ do
              (code, _, err) <- parseRun "env" "%module M\n%env Int\nS :: ()\nS <- 'a' { () }\n" "a" []
              code @?= ExitFailure 1
              assertBool err ("does not support grammars with %env" `isInfixOf` err)
          , testCase "a verbatim block that imports a module of the user, with --ghc-arg" $ do
              dir <- treeWith "parse-user" [("lib/User/Value.hs", "module User.Value (V (..)) where\ndata V = V Int deriving (Show)\n"), ("G.peg", "%module G\n%{\nimport User.Value\n}%\n\nS :: V\nS <- 'a' { V 1 }\n"), ("in.txt", "a")]
              (code, out, err) <- parseIn dir ["parse", "G.peg", "in.txt", "--ghc-arg", "-i" <> (dir </> "lib")]
              (code, out, err) @?= (ExitSuccess, "V 1\n", "")
          , testCase "a second parse with the same grammar does not compile" $ do
              base <- testDir
              removePathForcibly (base </> "parse-cache-parse-cache")
              _ <- parseRun "cache" exprGrammar "1" []
              n1 <- compiles "parse-cache"
              _ <- parseRun "cache" exprGrammar "1 + 2" []
              n2 <- compiles "parse-cache"
              _ <- parseRun "cache" (exprGrammar <> "\n# changed\n") "1" []
              n3 <- compiles "parse-cache"
              (n2 - n1, n3 - n2) @?= (0, 1)
          , testCase "the embedded sources are those of peg-runtime and the pretty-printer" $ do
              exists <- doesDirectoryExist "../peg-runtime/src"
              when exists $ do
                files <- mapM (\(f, _) -> readFile ("../peg-runtime/src" </> f)) runtimeSources
                assertBool "run scripts/regen-fixtures.sh" (files == map snd runtimeSources)
                pretty' <- readFile "app/Pretty.hs"
                assertBool "run scripts/regen-fixtures.sh" (pretty' == prettySource)
          , testProperty "the pretty-printer keeps the tokens of show" $
              forAll genShown $ \s -> filter (not . isSpace) (pretty s) === filter (not . isSpace) s
          , testProperty "the pretty-printer indents a line at least as deep as its brackets" $
              forAll genLong $ \s -> let out = pretty s in counterexample out (all (\(d, l) -> contentColumn l >= d) (zip (depths (lines out)) (lines out)))
          , testCase "the pretty-printer indents along the brackets" $
              pretty (show [(i, replicate 3 (Just (show i))) | i <- [1 :: Int .. 3]])
                @?= unlines
                  [ "[ (1,[Just \"1\",Just \"1\",Just \"1\"])"
                  , ", (2,[Just \"2\",Just \"2\",Just \"2\"])"
                  , ", (3,[Just \"3\",Just \"3\",Just \"3\"])"
                  , "]"
                  ]
          ]
      , testGroup
          "files and UTF-8 (ADR 0045)"
          [ testCase "a missing file is one line and hints, without a backtrace, in every command" $ do
              dir <- treeWith "file-missing" [("G.peg", formatted), ("in.txt", "a")]
              forM_ [["gen", "nope.peg"], ["fmt", "nope.peg"], ["lint", "nope.peg"], ["parse", "nope.peg", "in.txt"]] $ \args -> do
                (code, out, err) <- pegHsIn dir args
                (code, out) @?= (ExitFailure 1, "")
                take 1 (lines err) @?= ["peg-hs: cannot read nope.peg: no such file"]
                assertBool err (all ("hint: " `isPrefixOf`) (drop 1 (lines err)))
                assertBool err (not ("CallStack" `isInfixOf` err || "backtrace" `isInfixOf` err || "openFile" `isInfixOf` err))
          , testCase "a missing input of parse is reported before compiling" $ do
              dir <- treeWith "file-missing-input" [("G.peg", formatted)]
              (code, _, err) <- pegHsIn dir ["parse", "G.peg", "nope.txt"]
              code @?= ExitFailure 1
              take 1 (lines err) @?= ["peg-hs: cannot read nope.txt: no such file"]
          , testCase "the hints of a missing file name a missing directory and the current directory" $ do
              dir <- treeWith "file-missing-dir" []
              (_, _, err) <- pegHsIn dir ["gen", "sub/nope.peg"]
              lines (withoutDir dir err)
                @?= [ "peg-hs: cannot read sub/nope.peg: no such file"
                    , "hint: the directory sub does not exist either"
                    , "hint: the path is relative to the current directory <dir>"
                    ]
          , testCase "a directory given to gen and parse" $ do
              dir <- treeWith "file-directory" [("sub/G.peg", formatted), ("in.txt", "a")]
              (code, _, err) <- pegHsIn dir ["gen", "sub"]
              code @?= ExitFailure 1
              lines err @?= ["peg-hs: cannot read sub: is a directory", "hint: peg-hs gen takes a grammar file, not a directory"]
              (code', _, err') <- pegHsIn dir ["parse", "sub", "in.txt"]
              code' @?= ExitFailure 1
              take 1 (lines err') @?= ["peg-hs: cannot read sub: is a directory"]
          , testCase "a file without permission to read" $ do
              dir <- treeWith "file-permission" [("G.peg", formatted)]
              let file = dir </> "G.peg"
              old <- getPermissions file
              bracket_ (setPermissions file emptyPermissions) (setPermissions file old) $ do
                canRead <- (True <$ readFile file) `catchIOAny` pure False
                unless canRead $ do
                  (code, _, err) <- pegHsIn dir ["gen", "G.peg"]
                  (code, lines err) @?= (ExitFailure 1, ["peg-hs: cannot read G.peg: permission denied"])
          , testCase "gen -o into a missing directory" $ do
              dir <- treeWith "file-write" [("G.peg", formatted)]
              (code, out, err) <- pegHsIn dir ["gen", "G.peg", "-o", "out/M.hs"]
              (code, out) @?= (ExitFailure 1, "")
              lines err @?= ["peg-hs: cannot write out/M.hs: directory out does not exist", "hint: peg-hs does not create directories; create out first"]
          , testCase "fmt and lint report a missing file and go on with the others" $ do
              dir <- treeWith "file-go-on" [("B.peg", unformatted)]
              (code, _, err) <- pegHsIn dir ["fmt", "nope.peg", "B.peg"]
              code @?= ExitFailure 1
              take 1 (lines err) @?= ["peg-hs: cannot read nope.peg: no such file"]
              readFile (dir </> "B.peg") >>= (@?= formatted)
              (code', _, err') <- pegHsIn dir ["lint", "nope.peg", "B.peg"]
              code' @?= ExitFailure 1
              filter (not . ("hint: " `isPrefixOf`)) (lines err') @?= ["peg-hs: cannot read nope.peg: no such file"]
          , testCase "fmt and lint take a directory, and walk it" $ do
              dir <- treeWith "file-walk-dir" [("sub/deeper/B.peg", unformatted), ("A.peg", unformatted)]
              (code, _, _) <- pegHsIn dir ["fmt", "sub"]
              code @?= ExitSuccess
              readFile (dir </> "sub/deeper/B.peg") >>= (@?= formatted)
              readFile (dir </> "A.peg") >>= (@?= unformatted)
              (code', _, err') <- pegHsIn dir ["lint", "sub"]
              (code', err') @?= (ExitSuccess, "")
          , goldenVsString "the errors of files" "test/golden/file-errors.txt" $ do
              dir <- treeWith "file-golden" [("G.peg", formatted), ("sub/H.peg", formatted), ("bad.peg", "%module M\n")]
              BS.writeFile (dir </> "bad.peg") (BS.pack ([0x25, 0x6D, 0x0A, 0xE3, 0x81]))
              outs <-
                mapM
                  (errorsIn dir)
                  [ ["gen", "nope.peg"]
                  , ["gen", "sub/nope/G.peg"]
                  , ["gen", "sub"]
                  , ["gen", "G.peg", "-o", "out/M.hs"]
                  , ["gen", "bad.peg"]
                  , ["fmt", "nope.peg"]
                  , ["lint", "nope.peg"]
                  , ["parse", "sub", "G.peg"]
                  , ["parse", "G.peg", "nope.txt"]
                  ]
              pure (BL.pack (concat outs))
          , testCase "a file that is not UTF-8 names the byte" $ do
              dir <- treeWith "file-utf8" []
              BS.writeFile (dir </> "bad.peg") (BS.pack (map (fromIntegral . fromEnum) "%module M\n" ++ [0xFF]))
              (code, _, err) <- pegHsIn dir ["gen", "bad.peg"]
              code @?= ExitFailure 1
              take 1 (lines err) @?= ["peg-hs: cannot read bad.peg: not UTF-8 (at byte 11)"]
          , testCase "gen, fmt and lint read and write Japanese in the C locale" $ do
              dir <- treeWith "file-c-locale" []
              let bytes = TE.encodeUtf8 (T.pack japaneseGrammar)
              BS.writeFile (dir </> "G.peg") bytes
              (genCode, _, genErr) <- pegHsBytes dir cLocale ["gen", "G.peg", "-o", "G.hs"]
              (genCode, genErr) @?= (ExitSuccess, BS.empty)
              generated <- BS.readFile (dir </> "G.hs")
              _ <- pegHsBytes dir [] ["gen", "G.peg", "-o", "G-utf8.hs"]
              inUtf8 <- BS.readFile (dir </> "G-utf8.hs")
              -- The same module as in a UTF-8 locale, but for its own name.
              generated @?= replaceBytes "G-utf8.hs" "G.hs" inUtf8
              (fmtCode, _, fmtErr) <- pegHsBytes dir cLocale ["fmt", "G.peg"]
              (fmtCode, fmtErr) @?= (ExitSuccess, BS.empty)
              BS.readFile (dir </> "G.peg") >>= (@?= bytes)
              (lintCode, _, lintErr) <- pegHsBytes dir cLocale ["lint", "G.peg"]
              (lintCode, lintErr) @?= (ExitSuccess, BS.empty)
          , testCase "the errors of a Japanese grammar are UTF-8 in the C locale" $ do
              dir <- treeWith "file-c-locale-error" []
              BS.writeFile (dir </> "G.peg") (TE.encodeUtf8 (T.pack "%module M\nS :: ()\nS <- 未定義 { () }\n"))
              (code, _, err) <- pegHsBytes dir cLocale ["gen", "G.peg"]
              code @?= ExitFailure 1
              assertBool (show err) (TE.encodeUtf8 (T.pack "undefined rule 未定義") `BS.isInfixOf` err)
          , testCase "a byte order mark is skipped" $ do
              a <- treeWith "file-bom-a" []
              b <- treeWith "file-bom-b" []
              BS.writeFile (a </> "G.peg") (TE.encodeUtf8 (T.pack formatted))
              BS.writeFile (b </> "G.peg") (BS.pack [0xEF, 0xBB, 0xBF] <> TE.encodeUtf8 (T.pack formatted))
              _ <- pegHsIn a ["gen", "G.peg"]
              (code, _, err) <- pegHsIn b ["gen", "G.peg"]
              (code, err) @?= (ExitSuccess, "")
              ga <- BS.readFile (a </> "G.hs")
              gb <- BS.readFile (b </> "G.hs")
              ga @?= gb
          , testCase "parse reads and shows Japanese in the C locale" $ do
              dir <- treeWith "parse-c-locale" []
              BS.writeFile (dir </> "G.peg") (TE.encodeUtf8 (T.pack japaneseGrammar))
              BS.writeFile (dir </> "in.txt") (TE.encodeUtf8 (T.pack "あいう。"))
              (base, e) <- parseEnv "parse-c-locale"
              removePathForcibly (base </> "parse-cache-parse-c-locale")
              (code, out, err) <- pegHsBytes dir (cLocale ++ [(k, v) | (k, v) <- e, k `elem` ["PATH", "XDG_CACHE_HOME", "PEG_TEST_GHC_LOG"]]) ["parse", "G.peg", "in.txt", "--format", "cst"]
              (code, err) @?= (ExitSuccess, BS.empty)
              assertBool (show out) (TE.encodeUtf8 (T.pack "あいう") `BS.isInfixOf` out)
          , testCase "the output of show with text in any language is readable" $ do
              readable (show "あ1\SOH") @?= "\"あ1\\SOH\""
              readable (show ("a\\12354" :: String)) @?= show ("a\\12354" :: String)
              readable "S@0..3 TEXT \"\\12354\"" @?= "S@0..3 TEXT \"あ\""
          , testProperty "readable keeps the value of show" $
              \s -> (read (readable (show (s :: String))) :: String) === s
          , testCase "the versions of GHC that parse takes" $ do
              map supportedGhc ["9.10.3", "9.12.2", "9.14.1"] @?= [True, True, True]
              map supportedGhc ["9.8.4", "9.16.1", "9.1", "10.0.1", ""] @?= replicate 5 False
          , testProperty "the first byte that is not UTF-8 is where the decoder of text fails" $
              forAll genBytes $ \bs -> case utf8ErrorOffset bs of
                Nothing -> isRight (TE.decodeUtf8' bs)
                Just i -> not (isRight (TE.decodeUtf8' bs)) && isRight (TE.decodeUtf8' (BS.take i bs))
          , testCase "the position of the byte counts the byte order mark" $
              decodeUtf8File (BS.pack [0xEF, 0xBB, 0xBF, 0x41, 0xFF]) @?= Left 5
          ]
      , testGroup
          "gen (ADR 0028)"
          [ testCase "an unsafe label is a warning" $ do
              (code, _, err, written) <- genOn "warn" unsafe []
              code @?= ExitSuccess
              assertBool err ("3:11: warning: the label l may reject valid input" `isInfixOf` err)
              assertBool "the module is written" written
          , testCase "--Werror fails on a warning" $ do
              (code, _, err, written) <- genOn "werror" unsafe ["--Werror"]
              code @?= ExitFailure 1
              assertBool err ("warning:" `isInfixOf` err)
              assertBool "no module is written" (not written)
          , testCase "%safe silences the warning" $ do
              (code, _, err, _) <- genOn "safe" (unsafe <> "%safe l\n") ["--Werror"]
              code @?= ExitSuccess
              err @?= ""
          , testCase "--strip-labels writes the grammar without labels as another module" $ do
              dir <- testDir
              (code, _, _, _) <- genOn "strip" unsafe ["--strip-labels", "N", "--Werror"]
              code @?= ExitSuccess
              out <- readFile (dir </> "strip.hs")
              assertBool "module N" ("module N" `isInfixOf` out)
              assertBool "no label" (not ("labeled" `isInfixOf` out))
          ]
      ]

catchIOAny :: IO a -> IO a -> IO a
catchIOAny act fallback = act `catchIOError'` const fallback
  where
    catchIOError' = Control.Exception.catch :: IO a -> (Control.Exception.IOException -> IO a) -> IO a

replaceBytes :: String -> String -> BS.ByteString -> BS.ByteString
replaceBytes old new = TE.encodeUtf8 . T.replace (T.pack old) (T.pack new) . TE.decodeUtf8

-- The output with <dir> for the directory, also where macOS reaches the
-- temporary directory through /private.
withoutDir :: FilePath -> String -> String
withoutDir dir = replace dir "<dir>" . replace ("/private" <> dir) "<dir>"
