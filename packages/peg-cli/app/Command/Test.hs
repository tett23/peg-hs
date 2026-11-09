{-# LANGUAGE OverloadedStrings #-}

-- | @peg-hs test@: parse the examples of a grammar and compare the results
-- with the expected ones (ADR 0091).
--
-- The examples of @NAME.hpeg@ are in the directory @NAME.cases@ beside it.
-- An example is an input @X.in@, parsed as it is (UTF-8, without a byte
-- order mark), with the expectation @X.cst@ (accepted, with this syntax
-- tree, as @peg-hs parse --format cst@ shows it) or @X.err@ (rejected,
-- with this error, as 'Peg.Runtime.renderParseError' writes it; an empty
-- @X.err@ compares only that the input is rejected). The examples in
-- @NAME.cases/RULE@ are parsed with the rule @RULE@ of @%entry@.
--
-- The examples are parsed by the interpreter of peg-grammar (ADR 0090),
-- without GHC. A grammar that the interpreter cannot parse with is
-- compiled as by @peg-hs parse@, unless it has @%env@: the way depends only
-- on the grammar.
module Command.Test
  ( testCommand
  , Outcome (..)
  , Way
  , interpretedWay
  , compiledWay
  , outcomeOf
  , expectationText
  ) where

import Command.Parse (Ghc, cacheBase, compiledParser, findGhc)
import Control.Exception (IOException, try)
import Control.Monad (forM, unless, when)
import Data.List (nub, sort)
import Data.Maybe (isJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Diagnostics (reportErrors)
import FileIO (readUtf8, reportFileError, writeUtf8)
import Files (grammarFiles)
import Options
import Peg.Grammar
import Peg.Grammar.Check (Analysis, check)
import Peg.Grammar.Interpret (Interpreter, interpret, interpreter, interpreterKindName)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Peg.Runtime (renderParseError)
import Peg.Runtime.Syntax (debugTree)
import qualified Pretty
import ProcessBytes (readProcessBytes)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory, removeFile)
import System.Exit (ExitCode (..))
import System.FilePath (dropExtension, takeExtension, (<.>), (</>))
import System.IO (hPutStrLn, stderr)

testCommand :: Command
testCommand =
  Command
    { cmdName = "test"
    , cmdSummary = "parse the examples of grammars and compare the results"
    , cmdArguments = "[GRAMMAR.hpeg|DIR...]"
    , cmdDescription =
        [ "Parse the examples of a grammar and compare the results with the expected ones. The"
        , "examples of NAME.hpeg are in the directory NAME.cases beside it: an input X.in, parsed as"
        , "it is, newline at the end included, and its expectation, X.cst or X.err. X.cst is the"
        , "syntax tree of an accepted input, as peg-hs parse --format cst shows it. X.err is the"
        , "error of a rejected input; an empty X.err compares only that the input is rejected."
        , "The examples in NAME.cases/RULE are parsed with the rule RULE of %entry. Other files are"
        , "ignored. A newline at the end of an expectation does not count."
        , ""
        , "A directory stands for the .hpeg files under it, and without arguments the .hpeg files"
        , "under the current directory are taken; the grammars found without NAME.cases are skipped."
        , "The failed examples are written to standard output, then the number of examples that"
        , "passed and failed."
        , ""
        , "The examples are parsed by interpreting the grammar, without ghc. A grammar that the"
        , "interpreter cannot parse with, such as one with a predicate it cannot evaluate, is"
        , "compiled with ghc as by peg-hs parse; a grammar with %env that the interpreter cannot"
        , "parse with is an error. Files are read and written as UTF-8."
        ]
    , cmdOptions =
        [ Opt "accept" Nothing Nothing "write the results as the expectations, and list the files"
        , Opt "ghc-arg" Nothing (Just "ARG") "pass ARG to ghc when the grammar is compiled (repeatable)"
        ]
    , cmdExamples =
        [ ("peg-hs test", "test the examples of every grammar under the current directory")
        , ("peg-hs test Expr.hpeg", "test the examples in Expr.cases")
        , ("peg-hs test --accept Expr.hpeg", "write the expectations of the examples in Expr.cases")
        ]
    , cmdRun = run
    }

-- | The result of parsing an input: accepted with the syntax tree, as
-- @peg-hs parse --format cst@ shows it (with a newline at the end), or
-- rejected with the error (one line, without a newline).
data Outcome = Accepted Text | Rejected Text
  deriving (Eq, Show)

-- | How the inputs of a grammar are parsed: by the interpreter, or by the
-- compiled parsers of the start rule ('Nothing') and the rules of
-- @%entry@.
data Way
  = Interpreted Interpreter
  | Compiled [(Maybe Text, FilePath)]

interpretedWay :: Interpreter -> Way
interpretedWay = Interpreted

-- | The compiled parsers of a checked grammar for the entries given, with
-- the ghc, the directory of the cache and the arguments to ghc given;
-- Nothing after reporting the errors of a build.
compiledWay :: Ghc -> FilePath -> FilePath -> Grammar -> Text -> [String] -> [Maybe Text] -> IO (Maybe Way)
compiledWay ghc base grammarFile g src ghcArgs entries = do
  exes <- forM (nub entries) $ \e -> fmap ((,) e) <$> compiledParser ghc base grammarFile g src False (T.unpack <$> e) ghcArgs
  pure (Compiled <$> sequence exes)

-- | Parse an input, the text of the file given, with an entry; or the
-- error of a compiled parser that did not end as a parser does.
outcomeOf :: Way -> Maybe Text -> FilePath -> Text -> IO (Either String Outcome)
outcomeOf way entry file text = case way of
  Interpreted ip ->
    pure . Right $ case interpret ip entry text of
      Left e -> Rejected (renderParseError e)
      Right tree -> Accepted (T.pack (Pretty.readable (T.unpack (debugTree (interpreterKindName ip) tree))))
  Compiled exes -> case lookup entry exes of
    Nothing -> pure (Left "no parser for the entry")
    Just exe -> do
      (code, out, err) <- readProcessBytes exe ["cst", file]
      pure $ case code of
        ExitSuccess -> Right (Accepted (TE.decodeUtf8Lenient out))
        ExitFailure 1 -> Right (Rejected (withoutNewline (TE.decodeUtf8Lenient err)))
        ExitFailure n -> Left ("the parser failed with " <> show n <> ": " <> T.unpack (TE.decodeUtf8Lenient err))

-- | The extension and the contents of the expectation of an outcome.
expectationText :: Outcome -> (String, Text)
expectationText = \case
  Accepted t -> ("cst", t)
  Rejected t -> ("err", t <> "\n")

-- The text without one newline at its end.
withoutNewline :: Text -> Text
withoutNewline t = maybe t id (T.stripSuffix "\n" t)

data Expect = ExpectCst | ExpectErr
  deriving (Eq)

-- An example: its entry, the path of its input without the extension, and
-- its expectation.
data Example = Example
  { exEntry :: Maybe Text
  , exBase :: FilePath
  , exExpect :: Maybe Expect
  }

-- The examples so far: those that passed, those that failed, and whether
-- there was an error (of a grammar, a file or the layout).
data Tally = Tally Int Int Bool

instance Semigroup Tally where
  Tally a b c <> Tally a' b' c' = Tally (a + a') (b + b') (c || c')

instance Monoid Tally where
  mempty = Tally 0 0 False

broken :: Tally
broken = Tally 0 0 True

run :: Parsed -> IO ExitCode
run p = do
  targets <- case parsedArguments p of
    [] -> map (\f -> (f, False)) <$> grammarFiles []
    args -> concat <$> mapM target args
  Tally passed failed errored <- mconcat <$> mapM (testGrammar accept ghcArgs) targets
  unless accept $ putStrLn (show passed <> " passed, " <> show failed <> " failed")
  pure (if failed > 0 || errored then ExitFailure 1 else ExitSuccess)
  where
    accept = flag "accept" p
    ghcArgs = [v | ("ghc-arg", v) <- parsedOptions p]
    -- A grammar given by name, or those found in a directory.
    target a = do
      isDir <- doesDirectoryExist a
      if isDir then map (\f -> (f, False)) <$> grammarFiles [a] else pure [(a, True)]

-- The directory of the examples of a grammar.
casesOf :: FilePath -> FilePath
casesOf file = dropExtension file <> ".cases"

-- Test the examples of a grammar, given by name or found.
testGrammar :: Bool -> [String] -> (FilePath, Bool) -> IO Tally
testGrammar accept ghcArgs (file, named) = do
  let cases = casesOf file
  hasCases <- doesDirectoryExist cases
  if not hasCases && not named
    then pure mempty
    else
      readUtf8 "peg-hs test takes grammar files and directories" file >>= \case
        Left e -> reportFileError e >> pure broken
        Right src
          | not hasCases -> failWith (file <> " has no examples: the directory " <> cases <> " does not exist")
          | otherwise -> case loadGrammar src of
              Left diags -> reportErrors file diags >> pure broken
              Right (g0, g, an) -> do
                (layoutErrors, examples) <- scanCases cases (map unLoc (grammarEntries g))
                mapM_ (hPutStrLn stderr . ("peg-hs: " <>)) layoutErrors
                let layout = if null layoutErrors then mempty else broken
                if null examples
                  then pure layout
                  else
                    wayOf file g0 g an src ghcArgs (map exEntry examples) >>= \case
                      Nothing -> pure broken
                      Just way -> (layout <>) . mconcat <$> mapM (runExample accept way) examples
  where
    failWith msg = hPutStrLn stderr ("peg-hs: " <> msg) >> pure broken

-- The grammar as written, expanded and checked, and its analysis.
loadGrammar :: Text -> Either [Diagnostic] (Grammar, Grammar, Analysis)
loadGrammar src =
  parseGrammar src >>= \g0 ->
    either (Left . templateNotes g0) (\(g, an) -> Right (g0, g, an)) (expandTemplates g0 >>= \g -> (,) g <$> check g)

-- How to parse the examples of a grammar: by the interpreter if it can
-- parse with the grammar, else compiled, but not a grammar with %env.
-- Nothing after reporting why the examples cannot be parsed.
wayOf :: FilePath -> Grammar -> Grammar -> Analysis -> Text -> [String] -> [Maybe Text] -> IO (Maybe Way)
wayOf file g0 g an src ghcArgs entries = case interpreter g an of
  Right ip -> pure (Just (interpretedWay ip))
  Left diags
    | isJust (grammarEnv g) -> do
        reportErrors file (templateNotes g0 diags)
        Nothing <$ hPutStrLn stderr ("peg-hs: " <> file <> ": the interpreter cannot parse with this grammar, and peg-hs test does not compile grammars with %env")
    | otherwise ->
        findGhc "test" >>= \case
          Left msg -> Nothing <$ hPutStrLn stderr ("peg-hs: " <> msg)
          Right ghc -> do
            base <- cacheBase
            compiledWay ghc base file g src ghcArgs entries

-- The examples in the directory of the examples of a grammar, with the
-- errors of their layout, in the order of their paths.
scanCases :: FilePath -> [Text] -> IO ([String], [Example])
scanCases cases entries = do
  (dirs, files) <- entriesOf cases
  let (errs, examples) = examplesIn Nothing cases files
  inner <- forM dirs $ \d -> do
    let path = cases </> d
    if T.pack d `notElem` entries
      then pure ([path <> ": " <> d <> " is not a rule of %entry; the examples of a rule of %entry go in the directory of its name"], [])
      else do
        (dirs', files') <- entriesOf path
        let (errs', examples') = examplesIn (Just (T.pack d)) path files'
        pure ([path </> d' <> ": a directory in the examples of the rule " <> d <> "; put its examples in " <> path | d' <- dirs'] ++ errs', examples')
  pure (errs ++ concatMap fst inner, examples ++ concatMap snd inner)
  where
    entriesOf dir = do
      names <- sort <$> listDirectory dir
      kinds <- forM names $ \n -> (,) n <$> doesDirectoryExist (dir </> n)
      pure ([n | (n, True) <- kinds], [n | (n, False) <- kinds])

-- The examples among the files of a directory, and the errors of their
-- layout. Files of other extensions are ignored.
examplesIn :: Maybe Text -> FilePath -> [FilePath] -> ([String], [Example])
examplesIn entry dir files =
  (concatMap errorsOf stems, [Example entry (dir </> s) (expectOf s) | s <- inputs, not (both s)])
  where
    with ext = [dropExtension f | f <- files, takeExtension f == ext]
    inputs = with ".in"
    csts = with ".cst"
    errs = with ".err"
    stems = sort (nub (inputs ++ csts ++ errs))
    both s = s `elem` csts && s `elem` errs
    expectOf s
      | s `elem` csts = Just ExpectCst
      | s `elem` errs = Just ExpectErr
      | otherwise = Nothing
    errorsOf s
      | s `notElem` inputs =
          [dir </> s <.> ext <> ": there is no input " <> s <.> "in" <> " for this expectation" | (ext, ss) <- [("cst", csts), ("err", errs)], s `elem` ss]
      | both s = [dir </> s <.> "in" <> ": both " <> s <.> "cst" <> " and " <> s <.> "err" <> " are given; keep the one that is expected"]
      | otherwise = []

-- Parse an example and compare the result, or with --accept write it.
runExample :: Bool -> Way -> Example -> IO Tally
runExample accept way ex =
  readUtf8 "" input >>= \case
    Left e -> reportFileError e >> pure broken
    Right text ->
      outcomeOf way (exEntry ex) input text >>= \case
        Left msg -> hPutStrLn stderr ("peg-hs: " <> input <> ": " <> msg) >> pure broken
        Right outcome
          | accept -> record ex outcome
          | otherwise -> compareWith ex outcome
  where
    input = exBase ex <.> "in"

-- Compare the outcome of an example with its expectation, and write the
-- failure to standard output.
compareWith :: Example -> Outcome -> IO Tally
compareWith ex outcome = case exExpect ex of
  Nothing -> failed [exBase ex <.> "in" <> ": no expectation; run peg-hs test --accept to record the result"]
  Just expect -> do
    let file = exBase ex <.> (if expect == ExpectCst then "cst" else "err")
    readUtf8 "" file >>= \case
      Left e -> reportFileError e >> pure broken
      Right expected0 ->
        let expected = withoutNewline expected0
         in case (expect, outcome) of
              (ExpectCst, Accepted t)
                | expected == withoutNewline t -> passed
                | otherwise ->
                    let (n, e, a) = firstDifference expected (withoutNewline t)
                     in failed [file <> ":" <> show n <> ": the syntax tree differs", "  expected:   " <> T.unpack e, "  actual:     " <> T.unpack a]
              (ExpectCst, Rejected r) -> failed [file <> ": expected acceptance, but " <> T.unpack r]
              (ExpectErr, Accepted _) -> failed [file <> ": expected a rejection, but the input was accepted"]
              (ExpectErr, Rejected r)
                | T.null expected || expected == r -> passed
                | otherwise ->
                    failed ([file <> ": the error differs"] ++ map (("  expected:   " <>) . T.unpack) (T.splitOn "\n" expected) ++ ["  actual:     " <> T.unpack r])
  where
    passed = pure (Tally 1 0 False)
    failed ls = mapM_ putStrLn ls >> pure (Tally 0 1 False)

-- The number (from 1) of the first line where two texts differ, and the
-- two lines; (end of file) for a text that ends before.
firstDifference :: Text -> Text -> (Int, Text, Text)
firstDifference = go 1 `on2` T.splitOn "\n"
  where
    on2 f h x y = f (h x) (h y)
    eof = "(end of file)"
    go :: Int -> [Text] -> [Text] -> (Int, Text, Text)
    go n (x : xs) (y : ys)
      | x == y = go (n + 1) xs ys
      | otherwise = (n, x, y)
    go n (x : _) [] = (n, x, eof)
    go n [] (y : _) = (n, eof, y)
    go n [] [] = (n, eof, eof)

-- Write the outcome of an example as its expectation, and remove the
-- expectation of the other kind; an expectation that the outcome meets is
-- kept as it is, and so is an empty X.err of a rejected input.
record :: Example -> Outcome -> IO Tally
record ex outcome = do
  let (ext, contents) = expectationText outcome
      file = exBase ex <.> ext
      other = exBase ex <.> (if ext == "cst" then "err" else "cst")
  current <- readUtf8 "" file
  let kept = case (current, outcome) of
        (Right t, Rejected _) | T.null (withoutNewline t) -> True
        (Right t, _) -> withoutNewline t == withoutNewline contents
        (Left _, _) -> False
  written <-
    if kept
      then pure (Right False)
      else fmap (const True) <$> writeUtf8 file contents
  case written of
    Left e -> reportFileError e >> pure broken
    Right w -> do
      when w (putStrLn ("wrote " <> file))
      hasOther <- doesFileExist other
      if not hasOther
        then pure (Tally 1 0 False)
        else
          try (removeFile other) >>= \case
            Right () -> putStrLn ("removed " <> other) >> pure (Tally 1 0 False)
            Left (err :: IOException) -> do
              hPutStrLn stderr ("peg-hs: cannot remove " <> other <> ": " <> show err)
              pure broken
