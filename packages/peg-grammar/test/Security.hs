{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the fixes of the security audit of 2026-11-07 (ADR 0080):
-- the values of @%module@ and @%export@ (SEC-05), and the limit on the
-- nesting of expressions (SEC-06).
module Security (securityTests) where

import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Assemble (Top (..), assemble)
import Peg.Grammar.Format (formatGrammar)
import Peg.Grammar.Parser (parseGrammar, parseTops)
import Test.Tasty
import Test.Tasty.HUnit

securityTests :: TestTree
securityTests =
  testGroup
    "security fixes (ADR 0080)"
    [ moduleTests
    , exportTests
    , nestingTests
    ]

-- The errors of a grammar as (line, column, message).
errorsAt :: Text -> [(Int, Int, Text)]
errorsAt src = case parseGrammar src of
  Left ds -> [(l, c, m) | Diagnostic (Loc _ l c) m <- ds]
  Right _ -> []

rule :: Text
rule = "S :: ()\nS <- 'a' { () }\n"

moduleTests :: TestTree
moduleTests =
  testGroup
    "the value of %module is a module name (SEC-05)"
    ( [ testCase ("rejects " <> show m) $
          errorsAt ("%module " <> m <> "\n" <> rule) @?= [(1, 9, "%module expects a module name, but got " <> m)]
      | m <- ["M (parse) where evil = 1 {-", "m", "M.", ".M", "M..N", "M N", "M\tN"]
      ]
        ++ [ testCase ("accepts " <> show m) $ errorsAt ("%module " <> m <> "\n" <> rule) @?= []
           | m <- ["M", "A.B.C", "A1.B_c'"]
           ]
    )

exportTests :: TestTree
exportTests =
  testGroup
    "the items of %export are export items (SEC-05)"
    ( [ testCase ("rejects " <> show x) $
          errorsAt ("%module M\n%export " <> x <> "\n" <> rule) @?= [(2, 9, "%export expects export items, but got " <> x)]
      | x <- ["evil2) where evil2 = 2 {-", "f --x", "(-->)", "x {- y -}", "x where", "Expr(..", "Expr(..))", "(a)", "module m", "type", "f g"]
      ]
        ++ [ testCase ("accepts " <> show x) $ errorsAt ("%module M\n%export " <> x <> "\n" <> rule) @?= []
           | x <-
               [ "Expr(..)"
               , "Expr(Add, Mul)"
               , "evalExpr"
               , "M.f"
               , "(+++)"
               , "type (:+)"
               , "pattern P"
               , "module Data.Text"
               , "Expr(..), evalExpr, M.f, (+++), type (:+), pattern P, module Data.Text"
               , "Expr( Add , Mul , (:+) )"
               , "( +++ )"
               , "Data.Map.Map(..)"
               ]
           ]
        ++ [ testCase "an item with a newline is an error" $
              let l = Loc 0 2 9
               in assemble [TDirective (Loc 0 1 1) "module" (Loc 0 1 9) "M", TDirective (Loc 0 2 1) "export" l "f\nevil = 1", TDef (Loc 0 3 1) "S" [] [Alt (Loc 0 3 6) [] Nothing Nothing]]
                    @?= Left [Diagnostic l "%export expects export items, but got f\nevil = 1"]
           , testCase "the second item is reported at its location" $
              errorsAt ("%module M\n%export f, g) where\n" <> rule) @?= [(2, 12, "%export expects export items, but got g) where")]
           ]
    )

-- A grammar whose rule S has the expression on line 2.
withRule :: Text -> Text
withRule e = "%module M\nS <- " <> e <> "\nT<p> :: ()\nT<p> <- p\n"

-- The column in line 2 of a grammar from withRule of the k-th occurrence
-- (from 1) of a text in the expression.
columnOf :: Int -> Text -> Text -> Int
columnOf k needle e = T.length "S <- " + T.length (T.intercalate needle (take k (T.splitOn needle e))) + 1

deeper :: Text
deeper = "the expression nests deeper than 256"

-- A kind of nesting: its expressions 256 and 257 levels deep, and the
-- text whose occurrence is the 257th level, if the kind has one.
nestings :: [(String, Text, Text, Maybe (Text, Int))]
nestings =
  [ ("groups", groups 256, groups 257, Just ("(", 257))
  , ("&", prefix "&" 256, prefix "&" 257, Just ("&", 257))
  , ("!", prefix "!" 256, prefix "!" 257, Just ("!", 257))
  , ("$", prefix "$" 256, prefix "$" 257, Just ("$", 257))
  , ("*", postfix "*" 256, postfix "*" 257, Just ("*", 257))
  , ("+", postfix "+" 256, postfix "+" 257, Just ("+", 257))
  , ("?", postfix "?" 256, postfix "?" 257, Just ("?", 257))
  , -- The label at the end is outside every group.
    ("labels", labels "'a'", labels "'a' ^l", Just ("^", 129))
  , ("template arguments", templates 256, templates 257, Just ("<", 257))
  , ("all of them", mixed "'a'", "!" <> mixed "'a'", Nothing)
  ]
  where
    groups n = T.replicate n "(" <> "'a'" <> T.replicate n ")"
    prefix op n = T.replicate n op <> "'a'"
    postfix op n = "'a'" <> T.replicate n op
    -- 128 groups, each with a label: 256 levels around the inner expression.
    labels inner = iterate (\e -> "(" <> e <> ") ^l") inner !! 128
    templates n = T.replicate n "T<" <> "'a'" <> T.replicate n ">"
    -- 64 times four levels: a template argument, a postfix operator, a
    -- group and a prefix operator.
    mixed inner = iterate (\e -> "T<(&" <> e <> ")?>") inner !! 64

nestingTests :: TestTree
nestingTests =
  testGroup
    "the nesting of expressions is limited to 256 levels (SEC-06)"
    ( concat
        [ [ testCase (name <> ": 256 levels are accepted") $ errorsAt (withRule ok) @?= []
          , testCase (name <> ": 257 levels are an error" <> maybe "" (const " at the 257th") at) $
              case at of
                Just (needle, k) -> errorsAt (withRule bad) @?= [(2, columnOf k needle bad, deeper)]
                Nothing -> map (\(l, _, m) -> (l, m)) (errorsAt (withRule bad)) @?= [(2, deeper)]
          ]
        | (name, ok, bad, at) <- nestings
        ]
        ++ [ testCase "parseTops rejects the grammar too" $
              either (map diagMessage) (const []) (parseTops (withRule (T.replicate 257 "(" <> "'a'" <> T.replicate 257 ")"))) @?= [deeper]
           , testCase "the formatter rejects the grammar" $
              either (map diagMessage) (const []) (formatGrammar (withRule (T.replicate 257 "!" <> "'a'"))) @?= [deeper]
           , testCase "a nesting of 100,000 levels is an error at the 257th" $
              errorsAt (withRule (T.replicate 100000 "(" <> "'a'" <> T.replicate 100000 ")")) @?= [(2, 6 + 256, deeper)]
           , testCase "the levels of expressions side by side are not added" $
              errorsAt (withRule (T.intercalate " / " (replicate 4 (T.replicate 200 "(" <> "'a'" <> T.replicate 200 ")")))) @?= []
           , testCase "the levels count from each rule" $
              errorsAt ("%module M\nS <- A " <> T.replicate 200 "(" <> "'a'" <> T.replicate 200 ")" <> "\nA <- " <> T.replicate 200 "(" <> "'b'" <> T.replicate 200 ")" <> "\n") @?= []
           ]
    )
