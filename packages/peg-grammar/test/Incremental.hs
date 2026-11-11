{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the parse by top-level fragments that the language server
-- reuses between versions (ADR 0071).
module Incremental (incrementalTests) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Grammar.Incremental
import Peg.Grammar.Outline (Outline (..), outline)
import Peg.Grammar.Parser (parseTops)
import Peg.Runtime (SyntaxError (..))
import Peg.Runtime.Syntax (debugTree)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

incrementalTests :: [FilePath] -> TestTree
incrementalTests files =
  testGroup
    "parsing by fragments (ADR 0071)"
    [ splitTests
    , testGroup
        "the same as the whole parse, for every grammar and its mutants"
        [ testCase f $ do
            src <- TIO.readFile f
            let fresh = parseFragments noFragments src
                bad =
                  [ m
                  | m <- src : mutants src
                  , -- Each mutant reuses the fragments of the grammar.
                    let p = parseFragments (parsedFragments fresh) m
                  , not (sameAsWhole m p)
                  ]
            assertBool (show (length bad) <> " mutants differ, the first:\n" <> concat [show m <> "\n" <> unlines (differences m (parseFragments (parsedFragments fresh) m)) | m <- take 1 bad]) (null bad)
        | f <- files
        ]
    , testProperty "a random sequence of edits: every version is the same as its whole parse" $
        withNumTests 300 $
          forAll (elements editBases) $ \base -> forAll (listOf1 (genEdit base)) $ \edits ->
            let versions = scanl (flip applyEdit) base edits
                -- The table with which each version is parsed: that of the
                -- version before it.
                tables = scanl (\table v -> parsedFragments (parseFragments table v)) noFragments versions
                failing = [(k, v, d) | (k, v, table) <- zip3 [0 :: Int ..] versions tables, let d = differences v (parseFragments table v), not (null d)]
             in counterexample (concat ["version " <> show k <> " of 0 to " <> show (length versions - 1) <> ":\n" <> show v <> "\nfragments: " <> show (splitFragments v) <> "\n" <> unlines d | (k, v, d) <- take 1 failing]) (null failing)
    , testCase "a change of one character inside a rule parses one or two fragments" $ do
        src <- TIO.readFile "grammar/Peg.hpeg"
        let p0 = parseFragments noFragments src
            edit = T.replace "Ident ':' !':'" "Ident ':' !':' " src
            p1 = parseFragments (parsedFragments p0) edit
        assertBool "the edit changes the text" (edit /= src)
        assertBool "fragments of the grammar" (parsedNew p0 > 50)
        assertBool ("reparsed: " <> show (parsedNew p1)) (parsedNew p1 >= 1 && parsedNew p1 <= 2)
        assertBool "the same as the whole parse" (sameAsWhole edit p1)
        -- The same text again parses nothing.
        parsedNew (parseFragments (parsedFragments p1) edit) @?= 0
    , testCase "the table keeps only the fragments of the latest version" $ do
        let a = "%module M\nA <- 'a'\nB <- 'b'\n"
            b = "%module M\nA <- 'a'\nC <- 'c'\n"
            p = parseFragments (parsedFragments (parseFragments noFragments a)) b
        fragmentTexts (parsedFragments p) @?= ["%module M\n", "A <- 'a'\n", "C <- 'c'\n"]
    , testCase "a character literal with an escape runs across lines (ADR 0094)" $ do
        -- The whole text has no error: the action of A ends on the last line.
        let src = "%module M\nA <- 'a' { { '\\x ) }\nB <- 'b' } }\n"
        assertBool (unlines (differences src (parseFragments noFragments src))) (sameAsWhole src (parseFragments noFragments src))
    , testCase "the syntax errors of the outline of the counterexample of CI on PR 82 (ADR 0094)" $ do
        let src = "module/\nX <-\n{{ / '\\t)* { () }{ # c\nx -}B\n <- \nT<&p}> : ()\nT<$}}\nX <- 'x'\n}%\n"
        map show (outlineSyntaxErrors (parsedOutline (parseFragments noFragments src))) @?= map show (outlineSyntaxErrors (outline src))
    , testCase "a quote inside an identifier does not start a character literal (ADR 0094)" $
        open "x' ( y'" @?= True
    , testCase "a line that continues the previous rule is parsed with it" $ do
        let src = "%module M\nA <- 'a'\nB\nC <- 'c' (\nD <- 'd'\n"
        assertBool "same" (sameAsWhole src (parseFragments noFragments src))
    ]

splitTests :: TestTree
splitTests =
  testGroup
    "splitting into fragments"
    [ testCase "rules, directives and comments" $
        splitFragments "%module M\n# a comment\n\nA :: Int\nA <- 'a' { 1 }\n  # indented\n"
          @?= ["%module M\n# a comment\n\n", "A :: Int\n", "A <- 'a' { 1 }\n  # indented\n"]
    , testCase "a comment or blank lines at the start" $
        splitFragments "# head\n\n%module M\n" @?= ["# head\n\n", "%module M\n"]
    , testCase "an alternative on the next line starting with /" $
        splitFragments "A <- 'a'\n/ 'b'\n  / 'c'\nB <- 'b'" @?= ["A <- 'a'\n/ 'b'\n  / 'c'\n", "B <- 'b'"]
    , testCase "lines at the start of the line inside a verbatim block" $
        splitFragments "%{\nimport X\nf :: Int\n}% \nA <- 'a'\n" @?= ["%{\nimport X\nf :: Int\n}% \n", "A <- 'a'\n"]
    , testCase "an unterminated verbatim block runs to the end" $
        splitFragments "%{\nimport X\nA <- 'a'\n" @?= ["%{\nimport X\nA <- 'a'\n"]
    , testCase "a multi-line action is split at a line that starts at the start of the line" $
        splitFragments "A <- 'a' {\n  1\n}\nB <- 'b'\n" @?= ["A <- 'a' {\n  1\n", "}\n", "B <- 'b'\n"]
    , testCase "carriage returns and tabs continue the fragment" $
        splitFragments "A <- 'a'\r\n\t/ 'b'\r\nB <- 'b'\r\n" @?= ["A <- 'a'\r\n\t/ 'b'\r\n", "B <- 'b'\r\n"]
    , testCase "the empty text" $
        splitFragments "" @?= []
    , testProperty "the fragments are the text" $
        forAll genText $ \t -> T.concat (splitFragments t) === t
    ]

-- The parse by fragments is the same as the whole parse: the typed items,
-- the syntax tree, its errors and the outline.
sameAsWhole :: Text -> Parsed -> Bool
sameAsWhole src = null . differences src

-- What differs from the whole parse.
differences :: Text -> Parsed -> [String]
differences src p =
  let (root, errs) = parseSyntaxWhole src
      (root', errs') = parsedSyntax p
      key e = (syntaxErrorLabel e, syntaxErrorRange e, syntaxErrorPos e)
   in [ "typed items: " <> show (parsedTops p) <> " instead of " <> show (parseTops src) | parsedTops p /= parseTops src ]
        ++ [ "tree:\n" <> T.unpack (debugTree syntaxKindName root') <> "instead of\n" <> T.unpack (debugTree syntaxKindName root) | debugTree syntaxKindName root' /= debugTree syntaxKindName root ]
        ++ [ "errors: " <> show (map key errs') <> " instead of " <> show (map key errs) | map key errs' /= map key errs ]
        ++ [ "outline" | parsedOutline p /= outline src ]

-- One character deleted or duplicated, at about 50 positions of a file: the
-- mutants of the test of the syntax tree with recovery (ADR 0035).
mutants :: Text -> [Text]
mutants src =
  concat
    [ [T.take i src <> T.drop (i + 1) src, T.take (i + 1) src <> T.drop i src]
    | i <- [0, step .. T.length src - 1]
    ]
  where
    step = max 1 (T.length src `div` 50)

-- An edit: insert a text at a position, or delete a range, counted in
-- characters of the version it applies to.
data Edit = Insert Int Text | Delete Int Int
  deriving (Show)

applyEdit :: Edit -> Text -> Text
applyEdit (Insert i s) t = T.take i t <> s <> T.drop i t
applyEdit (Delete i n) t = T.take i t <> T.drop (i + n) t

-- Edits of characters and lines at random positions. The position is a
-- fraction of the length, so that it fits any version.
genEdit :: Text -> Gen Edit
genEdit base = do
  let n = T.length base
  i <- choose (0, n)
  oneof
    [ Insert i . T.singleton <$> elements "a(){}'\"/#<-:% \n^$&!*[]"
    , Insert i <$> elements ["\n", "\nX <- 'x'\n", "\nA", "B <- ", " / ", "{ x }", "%{\n", "}%\n", "# c\n", "\n  / 'y'"]
    , Delete i <$> choose (1, 3)
    , Delete i <$> choose (5, 40)
    ]

editBases :: [Text]
editBases =
  [ T.unlines
      [ "%module M"
      , "%{"
      , "import Data.Char (isDigit)"
      , "}%"
      , ""
      , "# The sum."
      , "S :: Int"
      , "S <- a:N '+' b:N { a + b }"
      , "  / N"
      , ""
      , "N :: Int"
      , "N <- d:$[0-9]+ { read (T.unpack d) }"
      , ""
      , "W <- (' ' / '\\t')* { () }"
      , "T<p> :: ()"
      , "T<p> <- p W"
      ]
  , T.unlines
      [ "%module N"
      , "%start A"
      , "A :: [Text]"
      , "A <- x:B y:C {"
      , "  [x, y]"
      , "  }"
      , "B :: Text"
      , "B <- $('b' (C / D)*) ^lb"
      , "C :: Text"
      , "C <- \"c\" { \"c\" }"
      , "D <- &'d' !'e' . { () }"
      ]
  ]

genText :: Gen Text
genText = T.pack <$> listOf (elements "ab %{}\n\t\r/#<-")
