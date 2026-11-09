{-# LANGUAGE OverloadedStrings #-}

-- | Tests of @%expect@ and @%message@ (ADR 0089).
module ExpectMessage (expectMessageTests) where

import Data.Text (Text)
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Format (formatGrammar)
import Peg.Grammar.Highlight
import Peg.Grammar.Labels (stripLabels)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import Test.Tasty
import Test.Tasty.HUnit

expectMessageTests :: TestTree
expectMessageTests =
  testGroup
    "%expect and %message (ADR 0089)"
    [ testCase "the values go to the grammar" $ do
        let src = "%module M\n%expect A \"an a\"   # comment\n%message l \"x # y \\\"q\\\" \\u{41}\\-\\[\\]\\'\\\\\"\nA <- 'a' ^l\n"
        g <- either (assertFailure . show) pure (parseGrammar src)
        grammarExpects g @?= [(Located (Loc 2 9) "A", Located (Loc 2 11) "an a")]
        grammarMessages g @?= [(Located (Loc 3 10) "l", Located (Loc 3 12) "x # y \"q\" A-[]'\\")]
    , testGroup
        "errors"
        [ errorCase "no string" "%expect A" [(2, 1, "%expect expects a rule name and a string")]
        , errorCase "no rule name" "%expect \"a\"" [(2, 1, "%expect expects a rule name and a string")]
        , errorCase "something after the string" "%expect A \"a\" b" [(2, 1, "%expect expects a rule name and a string")]
        , errorCase "a single-quoted string" "%expect A 'a'" [(2, 1, "%expect expects a rule name and a string")]
        , errorCase "a label without a string" "%message l" [(2, 1, "%message expects a label and a string")]
        , errorCase "no argument" "%message" [(2, 1, "%message needs an argument")]
        , errorCase "an unterminated string" "%expect A \"abc" [(2, 15, "unterminated literal")]
        , errorCase "an unknown escape" "%expect A \"a\\qb\"" [(2, 14, "unknown escape \\q")]
        , errorCase "\\u without {" "%expect A \"\\u0041\"" [(2, 14, "expected '{'")]
        , errorCase "\\u without }" "%expect A \"\\u{41\"" [(2, 17, "expected '}'")]
        , errorCase "\\u out of range" "%expect A \"\\u{110000}\"" [(2, 12, "invalid \\u escape")]
        , errorCase "an empty description" "%expect A \"\"" [(2, 11, "the description is empty")]
        , errorCase "an empty message" "%message l \"\"" [(2, 12, "the message is empty")]
        , errorCase "a control character" "%message l \"a\\tb\"" [(2, 12, "the message contains a control character")]
        , errorCase "a newline in a description" "%expect A \"a\\nb\"" [(2, 11, "the description contains a control character")]
        , errorCase "DEL" "%expect A \"\\u{7F}\"" [(2, 11, "the description contains a control character")]
        , errorCase "two %expect for a rule" "%expect A \"a\"\n%expect A \"b\"" [(3, 1, "duplicate %expect for rule A")]
        , errorCase "two %message for a label" "%message l \"a\"\n%message l \"b\"" [(3, 1, "duplicate %message for label l")]
        , errorCase "an undefined rule" "%expect B \"b\"" [(2, 9, "undefined rule B")]
        , testCase "a template" $
            errorsOf "%module M\n%expect T \"t\"\nA <- T<'a'> ^l\nT<x> :: ()\nT<x> <- x { () }\n" @?= [(2, 9, "the template T cannot be named in %expect")]
        , errorCase "a label that does not appear" "%message m \"m\"" [(2, 10, "the label m does not appear in the grammar")]
        ]
    , testCase "fmt keeps the inside of the string" $
        formatGrammar "%module M\n%message l \"a  # b\"   # c\n%expect   A \"x  y\"\n\nA <- 'a' ^l\n"
          @?= Right "%module M\n%message l \"a  # b\" # c\n%expect A \"x  y\"\n\nA <- 'a' ^l\n"
    , testCase "highlights" $ do
        let src = "%module M\n%expect A \"a # b\" # c\n%message l \"m\"\nA <- 'a' ^l\n"
            kinds = [HDirectiveRule, HDirectiveLabel, HLiteral, HComment, HDirectiveArgument]
        fmap (\hs -> [(hlKind h, pos (hlStart h), pos (hlEnd h)) | h <- hs, hlKind h `elem` kinds, locLine (hlStart h) `elem` [2, 3]]) (highlights src)
          @?= Just
            [ (HDirectiveRule, (2, 9), (2, 10))
            , (HLiteral, (2, 11), (2, 18))
            , (HComment, (2, 19), (2, 22))
            , (HDirectiveLabel, (3, 10), (3, 11))
            , (HLiteral, (3, 12), (3, 15))
            ]
    , testCase "stripLabels removes %message and keeps %expect" $ do
        g <- either (assertFailure . show) pure (parseGrammar "%module M\n%expect A \"an a\"\n%message l \"m\"\nA <- 'a' ^l\n")
        let s = stripLabels g
        map (unLoc . fst) (grammarExpects s) @?= ["A"]
        grammarMessages s @?= []
    ]
  where
    pos (Loc l c) = (l, c)

-- The errors of a grammar whose rule A has the label l, after the lines.
errorCase :: String -> Text -> [(Int, Int, Text)] -> TestTree
errorCase name ls expected = testCase name (errorsOf ("%module M\n" <> ls <> "\nA <- 'a' ^l\n") @?= expected)

errorsOf :: Text -> [(Int, Int, Text)]
errorsOf src = case parseGrammar src >>= expandTemplates >>= \g -> g <$ check g of
  Left ds -> [(locLine (diagLoc d), locColumn (diagLoc d), diagMessage d) | d <- ds]
  Right _ -> []
