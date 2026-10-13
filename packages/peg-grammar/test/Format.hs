{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the formatter (ADR 0032).
module Format (formatTests) where

import qualified Data.ByteString.Lazy as BL
import Data.Either (isLeft)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Grammar.Format (formatGrammar, grammarComments, sameGrammar)
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Data.List (nub)
import Shard (chunkedProperty, chunks)

formatTests :: [FilePath] -> TestTree
formatTests files =
  testGroup
    "formatter (ADR 0032)"
    ( [ goldenVsString "the style" "test/golden/format/output.peg" $ do
        src <- TIO.readFile "test/golden/format/input.txt"
        either (assertFailure . show) (pure . BL.fromStrict . TE.encodeUtf8) (formatGrammar src)
    , testCase "idempotent and meaning-preserving on the grammars of the repository" $ do
        rs <- mapM check files
        [(f, why) | (f, Just why) <- zip files rs] @?= []
    , testCase "comments survive" $ do
        src <- TIO.readFile "test/golden/format/input.txt"
        fmap grammarComments (formatGrammar src) @?= Right (grammarComments src)
    , testCase "comments everywhere survive, and the result is stable" $ do
        let src =
              T.unlines
                [ "# first"
                , "%module M # module"
                , "# before a rule"
                , "S :: () # not a comment: part of the type"
                , "S <- # after <-"
                , "  x:A # after an item"
                , "  # between items"
                , "  ( 'a' # in a group"
                , "  / 'b' # before /"
                , "  ) T<'c', # in template arguments"
                , "  'd'> { () } # after an action"
                , "  # before an alternative"
                , "  / 'e' { () }"
                , "# between rules"
                , "A :: ()"
                , "A <- 'a' { () }"
                , "T<p, q> :: ()"
                , "T<p, # in template parameters"
                , "  q> <- p q { () }"
                , "# last"
                ]
        out <- either (assertFailure . show) pure (formatGrammar src)
        grammarComments out @?= grammarComments src
        length (grammarComments src) @?= 14
        formatGrammar out @?= Right out
        assertBool "same grammar" (sameGrammar src out)
    , testCase "a grammar with a syntax error is not formatted" $
        assertBool "error" (isLeft (formatGrammar "%module M\nA :: ()\nA <- 'a { () }\n"))
    ]
      ++ chunkedProperty "spaces and line breaks between tokens do not change the result" 300 (\part ->
          forAll (variant part (elements files)) $ \f -> ioProperty $ do
            src <- TIO.readFile f
            pure $ forAll (variant part (perturb src)) $ \src' ->
              counterexample (T.unpack src') (formatGrammar src' === formatGrammar src)
        )
      ++ [ testCase "the parts of the split property check different inputs (ADR 0042)" $ do
            srcs <- mapM TIO.readFile files
            let first part =
                  let f = unGen (variant part (elements (zip files srcs))) (mkQCGen 42) 30
                   in (fst f, unGen (variant part (perturb (snd f))) (mkQCGen 42) 30)
            length (nub (map first [1 .. chunks])) @?= chunks
         ]
    )
  where
    check f = do
      src <- TIO.readFile f
      pure $ case formatGrammar src of
        Left e -> Just ("not formatted: " <> show e)
        Right out
          | not (sameGrammar src out) -> Just "the grammar changed"
          | formatGrammar out /= Right out -> Just "not idempotent"
          | grammarComments out /= grammarComments src -> Just "comments changed"
          | otherwise -> Nothing

-- Replace runs of spaces that follow a space between two tokens of a rule
-- with one to three spaces. Spaces inside literals, classes, comments,
-- Haskell fragments and directives are left alone: only a space directly
-- after an expression's last character and before another expression is
-- changed, which keeps the meaning.
--
-- Around the @<-@ of a definition, where the style has no line break, line
-- breaks are added too.
perturb :: Text -> Gen Text
perturb src = T.unlines <$> mapM line (T.lines src)
  where
    line l
      | inRule l = T.concat <$> mapM piece (T.splitOn " " l)
      | " <- " `T.isInfixOf` l, not (T.isPrefixOf " " l) = do
          sep <- elements [" <- ", "\n  <-\n    ", "  <-\n  ", "\n <- "]
          pure (T.replace " <- " sep l)
      | otherwise = pure l
    inRule l = " <- " `T.isInfixOf` l && not (any (`T.isInfixOf` l) ["'", "\"", "[", "{", "#", "(", "$"])
    piece p = (p <>) <$> elements [" ", "  ", "   "]
