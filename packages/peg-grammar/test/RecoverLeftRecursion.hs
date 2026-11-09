{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Tests of left recursion through recovery rules (ADR 0095): the check
-- treats @e ^l@ with @%recover l R@ as @e / R@, so that a recovering parse
-- that comes back to a rule at the same position ends.
module RecoverLeftRecursion (recoverLeftRecursionTests) where

import Control.Exception (SomeException, evaluate, finally, try)
import Control.Monad (filterM)
import Data.Char (isSpace)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import GHC.Conc (disableAllocationLimit, enableAllocationLimit, setAllocationCounter)
import Labels (genGrammar, grammar)
import Peg.Grammar
import Peg.Grammar.Check
import Peg.Grammar.Interpret
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Peg.Runtime (SyntaxError (..), renderParseError)
import Peg.Runtime.Syntax (debugTree)
import System.Directory (doesFileExist)
import System.Timeout (timeout)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

recoverLeftRecursionTests :: TestTree
recoverLeftRecursionTests =
  testGroup
    "left recursion through recovery rules (ADR 0095)"
    [ testCase "the left recursive rules" $ do
        map leftRecursive [grammarA, grammarB, grammarD, grammarE]
          @?= map Right [S.fromList ["S"], S.fromList ["R", "S"], S.fromList ["L"], S.fromList ["L"]]
    , testCase "A ends on aa" $ do
        r <- recovered grammarA "aa"
        r @?= ("0..2", [])
    , testCase "B ends on b" $ do
        r <- recovered grammarB "b"
        r @?= ("0..1", [(Just "l", (0, 1))])
    , testCase "D ends on (a)" $ do
        r <- recovered grammarD "(a)"
        r @?= ("0..3", [])
    , testCase "E ends on (aa) and (ab)" $ do
        aa <- recovered grammarE "(aa)"
        snd aa @?= []
        ab <- recovered grammarE "(ab)"
        snd ab @?= [(Nothing, (0, 4))]
    , testCase "the parse without recovery does not change" $ do
        let inputs = concatMap (\n -> map T.pack (sequence (replicate n "ab()x"))) [0 .. 6 :: Int]
        sequence_
          [ do
              with <- prepared src
              without <- prepared (withoutRecover src)
              let differ = [t | t <- inputs, parsed with t /= parsed without t]
              assertBool (T.unpack src <> "\ndiffers on " <> show (take 3 differ)) (null differ)
          | src <- [grammarA, grammarB, grammarD, grammarE]
          ]
    , testCase "a rule with parameters in left recursion through a recovery rule" $
        errorsOf
          ( syntaxGrammar
              ["%recover l R", "S <- 'a' ^l", "R <- P(1) / 'x'", "P(n :: Int) :: ()", "P <- S"]
          )
          @?= ["rule P takes parameters and cannot take part in left recursion"]
    , testCase "a %nomemo rule in left recursion through a recovery rule" $
        errorsOf (syntaxGrammar ["%recover l R", "%nomemo S", "S <- 'a' ^l", "R <- S / 'x'"])
          @?= ["rule S takes part in left recursion and must be memoised"]
    , testCase "the left recursive rules of the grammars with %recover in the repository" $ do
        present <- filterM (doesFileExist . fst) repositoryGrammars
        found <- mapM (\(f, _) -> (,) f . leftRecursive <$> TIO.readFile f) present
        found @?= [(f, Right (S.fromList lr)) | (f, lr) <- present]
    , testProperty "a recovering parse of a random grammar ends" $
        withNumTests 300 $
          forAll recoverGrammar $ \src -> case prepare src of
            Left _ -> discard
            Right ip -> ioProperty $ do
              r <- bounded (sum [T.length d + length es | t <- shortInputs, let (d, es) = recoveredOf ip t])
              pure (counterexample (T.unpack src) (either (\m -> counterexample m False) (const (property True)) r))
    ]
  where
    shortInputs = concatMap (\n -> map T.pack (sequence (replicate n "abc"))) [0 .. 3 :: Int]

-- The grammars of the ADR.
grammarA, grammarB, grammarD, grammarE :: Text
grammarA = syntaxGrammar ["%recover l E", "S <- ('a' ^l) S / !.", "E <- ''"]
grammarB = syntaxGrammar ["%recover l R", "S <- 'a' ^l", "R <- S / 'x'"]
grammarD = syntaxGrammar ["%recover l E", "S <- '(' L ')'", "L <- (Item ^l) L / ''", "Item <- 'a'", "E <- &')'"]
grammarE = syntaxGrammar ["%recover l E", "S <- '(' L", "L <- ('a' ^l) (')' / L)", "E <- ''"]

syntaxGrammar :: [Text] -> Text
syntaxGrammar rs = grammar ("%syntax" : rs)

-- The grammar without its %recover lines; the labels stay. The recovery
-- rules become entry rules, so that they stay reachable.
withoutRecover :: Text -> Text
withoutRecover = T.unlines . map entry . T.lines
  where
    entry l = case T.words l of
      ["%recover", _, r] -> "%entry " <> r
      _ -> l

-- The grammars of the repository with %recover, and their left recursive
-- rules before ADR 0095, which it does not change.
repositoryGrammars :: [(FilePath, [Text])]
repositoryGrammars =
  [ ("../../conformance/bench/JsonRecover.hpeg", [])
  , ("../../conformance/bench/Memo.hpeg", ["AddExpr", "AndExpr", "MulExpr", "OrExpr"])
  , ("../../conformance/toml/Toml.hpeg", [])
  , ("../../editors/tree-sitter-hpeg/test/highlight/notation.hpeg", ["Expr"])
  , ("../peg-codegen/test/derived/RecoverExports.hpeg", [])
  , ("../peg-codegen/test/derived/RecoverInsertLabeled.hpeg", [])
  , ("../peg-codegen/test/fixtures/Expect.hpeg", [])
  , ("../peg-codegen/test/fixtures/ExpectSyntax.hpeg", [])
  , ("../peg-codegen/test/fixtures/Recover.hpeg", [])
  , ("../peg-codegen/test/fixtures/RecoverInsert.hpeg", [])
  , ("../peg-codegen/test/fixtures/RecoverShared.hpeg", [])
  , ("grammar/PegSyntax.hpeg", [])
  ]

-- Random grammars of the label tests with a recovery rule for l, which
-- calls the rules of the grammar or not, and matches the empty string or
-- not.
recoverGrammar :: Gen Text
recoverGrammar = do
  src <- genGrammar
  let names = filter (\n -> (n <> " <- ") `T.isInfixOf` src) ["S", "A", "B"]
  k <- choose (1, 2)
  alts <- vectorOf k (oneof [elements ["''", "'c'", "(!'a' .)*", "'b' 'c'"], elements names, (<> "?") <$> elements names, ("'b' " <>) <$> elements names])
  pure (src <> T.unlines ["%recover l R", "R :: ()", "R <- " <> T.intercalate " / " [a <> " { () }" | a <- alts]])

-- Parse, expand and check a grammar.
analysed :: Text -> Either [Diagnostic] (Grammar, Analysis)
analysed src = do
  g0 <- parseGrammar src
  g <- either (Left . templateNotes g0) Right (expandTemplates g0)
  an <- either (Left . templateNotes g0) Right (check g)
  pure (g, an)

leftRecursive :: Text -> Either [Diagnostic] (S.Set Text)
leftRecursive = fmap (analysisLeftRecursive . snd) . analysed

errorsOf :: Text -> [Text]
errorsOf = either (map (\(Diagnostic _ m) -> m)) (const []) . analysed

prepare :: Text -> Either [Diagnostic] Interpreter
prepare src = analysed src >>= uncurry interpreter

prepared :: Text -> IO Interpreter
prepared src = either (\ds -> assertFailure (show ds) >> error "unreachable") pure (prepare src)

parsed :: Interpreter -> Text -> Either Text Text
parsed ip = either (Left . renderParseError) (Right . debugTree (interpreterKindName ip)) . interpret ip Nothing

-- The range of the tree, and the labels and ranges of the errors.
recoveredOf :: Interpreter -> Text -> (Text, [(Maybe Text, (Int, Int))])
recoveredOf ip t =
  let (tree, errs) = interpretRecover ip Nothing t
   in (T.takeWhile (not . isSpace) (T.drop 1 (T.dropWhile (/= '@') (debugTree (interpreterKindName ip) tree))), [(syntaxErrorLabel e, syntaxErrorRange e) | e <- errs])

recovered :: Text -> Text -> IO (Text, [(Maybe Text, (Int, Int))])
recovered src t = do
  ip <- prepared src
  r <- bounded (let x@(d, es) = recoveredOf ip t in T.length d `seq` length (show es) `seq` x)
  either assertFailure pure r

-- Evaluate a value within 5 seconds and 2 GB of allocation, so that a
-- parse that does not end fails the test instead of hanging or exhausting
-- the memory.
bounded :: a -> IO (Either String a)
bounded x = do
  r <- try $ timeout 5_000_000 $ do
    setAllocationCounter 2_000_000_000
    enableAllocationLimit
    evaluate x `finally` disableAllocationLimit
  pure $ case r of
    Left e -> Left ("the parse did not end: " <> show (e :: SomeException))
    Right Nothing -> Left "the parse did not end in 5 seconds"
    Right (Just v) -> Right v
