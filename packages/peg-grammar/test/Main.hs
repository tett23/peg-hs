{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Check
import Peg.Grammar.Parser
import qualified Data.Text.IO as TIO
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeExtension, (</>))
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = do
  files <- grammarFiles
  defaultMain $
    testGroup
      "peg-grammar"
      [ notationTests
      , checkTests
      , analysisTests
      , selfHostingTests files
      ]

-- Every grammar in the repository. Directories outside this package are
-- missing when the tests run from a source tarball, and are skipped.
grammarFiles :: IO [FilePath]
grammarFiles = concat <$> mapM pegsIn dirs
  where
    dirs =
      [ "grammar"
      , "../peg-codegen/test/fixtures"
      , "../../conformance/json"
      , "../../conformance/bench"
      , "../../conformance/commonmark"
      , "../../conformance/commonmark/v1"
      ]
    pegsIn d = do
      exists <- doesDirectoryExist d
      if exists
        then map (d </>) . filter ((== ".peg") . takeExtension) <$> listDirectory d
        else pure []

-- The self-hosted parser must return exactly the grammar the hand-written
-- parser returns, locations included (the migration test of the
-- specification's self-hosting principle).
selfHostingTests :: [FilePath] -> TestTree
selfHostingTests files =
  testGroup
    "self-hosting"
    ( [ testCase f $ do
          src <- TIO.readFile f
          let expected = parseGrammar src
          assertBool ("the hand-written parser rejects " <> f) (either (const False) (const True) expected)
          parseGrammarSelfHosted src @?= expected
      | f <- files
      ]
        ++ [ testCase ("snippet " <> show i) (parseGrammarSelfHosted src @?= parseGrammar src)
           | (i, src) <- zip [1 :: Int ..] validSnippets
           ]
        ++ [ testCase ("rejected snippet " <> show i) $
               assertBool "both parsers should reject" (isLeft (parseGrammarSelfHosted src) && isLeft (parseGrammar src))
           | (i, src) <- zip [1 :: Int ..] invalidSnippets
           ]
    )
  where
    isLeft = either (const True) (const False)
    validSnippets =
      [ "%module A.B\n%start S\n%entry T\n%export X(..), y\n%env Set Text\n%tabstop 4\n%{\nimport X\n}%\nS :: ()\nS <- T\nT :: ()\nT <- 'a' { () }\n"
      , "# top\n%module M # trailing\nA :: () \nA <- '#' # not the literal\n  { () } # after\n"
      , "%module M\nA :: ()\nA <- $[0-9]+ !'a'* ^oops &{ n > 0 } !{ odd n } { () }\n"
      , "%module M\nA :: ()\nA <- '\\n\\t\\r\\\\\\'\\\"\\]\\[\\-\\u{3042}' \"x\" [a-z_\\-0-9] [-a] [a-] { () }\n"
      , "%module M\nA :: String\nA <- x:B 'c' y:$'d' { \"}{\" ++ ['}'] ++ f' }\nB :: String\nB <- 'b' { \"\" }\n"
      , "%module M\nA :: ()\nA <- B(1 + f (2, 3), x) B ('x') { () }\nB(n :: Int, c :: Char) :: ()\nB <- 'b' { () }\n"
      , "%module M\nA :: ()\nA <- B\n  C\nB :: ()\nB <- 'b' { () }\nC :: ()\nC <- ('c' / 'd' e:$'e')? { () }\n"
      , "%module M\n%{ import Y }%\nA :: Int\nA <- 'a' { let x = '\\'' in 1 }\n"
      , "%module M\n数式 :: Int\n数式 <- 値:項 '+' 次の値:項 { 値 + 次の値 }\n項 :: Int\n項 <- 'n' { 1 }\n"
      , "%module M\nÄußerung :: Text\nÄußerung\x3000<-\x3000größe:$'a'\x3000{ größe }\n"
      , "%module M\nA :: Int\nA <- 'a' { let é' = 'x' in length [é'] }\n"
      ]
    invalidSnippets =
      [ "%module M\nA :: ()\nA <- '\\q' { () }\n"
      , "%module M\nA :: ()\nA <- 'abc\n"
      , "%module M\nA :: ()\nA <- ('a' { () })\n"
      , "A :: ()\nA <- 'a' { () }\n"
      , "%module M\nA :: ()\nA <- { ( }\n"
      ]

parseOk :: Text -> IO Grammar
parseOk src = case parseGrammar src of
  Right g -> pure g
  Left ds -> assertFailure (show ds) >> error "unreachable"

-- The single alternative of the single rule of a grammar.
firstAlt :: Grammar -> Alt
firstAlt g = case grammarRules g of
  r : _ | a : _ <- ruleAlts r -> a
  _ -> error "no alternative"

exprs :: Text -> IO [Expr]
exprs body = map itemExpr . altItems . firstAlt <$> parseOk ("%module M\nA :: ()\nA <- " <> body <> "\n")

-- Errors of parsing and checking, as (line, column, message prefix).
errorsOf :: Text -> [(Int, Int)]
errorsOf src = case parseGrammar src >>= check of
  Left ds -> [(locLine l, locColumn l) | Diagnostic l _ <- ds]
  Right _ -> []

messagesOf :: Text -> [Text]
messagesOf src = case parseGrammar src >>= check of
  Left ds -> map diagMessage ds
  Right _ -> []

notationTests :: TestTree
notationTests =
  testGroup
    "notation (ADR 0004, 0005, 0012, 0014)"
    [ testCase "directives and verbatim blocks" $ do
        g <-
          parseOk
            "%module A.B\n%start S\n%entry T\n%export X(..), y\n%env Set Text\n%tabstop 4\n%{\nimport X\n}%\nS :: ()\nS <- T\nT :: ()\nT <- 'a' { () }\n"
        unLoc (grammarModule g) @?= "A.B"
        fmap unLoc (grammarStart g) @?= Just "S"
        map unLoc (grammarEntries g) @?= ["T"]
        map unLoc (grammarExports g) @?= ["X(..)", "y"]
        fmap unLoc (grammarEnv g) @?= Just "Set Text"
        fmap unLoc (grammarTabstop g) @?= Just 4
        map unLoc (grammarVerbatim g) @?= ["import X"]
        map locOf (grammarVerbatim g) @?= [Loc 8 1]
    , testCase "comments" $ do
        g <- parseOk "# top\n%module M # trailing\nA :: () \nA <- '#' # not the literal\n  { () } # after\n"
        exprs' g @?= [ELit "#" "'#'"]
    , testCase "precedence: suffix binds tighter than prefix" $
        exprs "$[0-9]+" >>= (@?= [ECapture (EPlus (EClass [('0', '9')] "[0-9]"))])
    , testCase "precedence: label between suffix and prefix" $ do
        es <- exprs "!'a'* ^oops"
        case es of
          [ENot (ELabel _ (EStar (ELit "a" "'a'")) "oops")] -> pure ()
          _ -> assertFailure (show es)
    , testCase "literals with escapes" $
        exprs "'\\n\\t\\r\\\\\\'\\\"\\]\\[\\-\\u{3042}' \"x\"" >>= (@?= [ELit "\n\t\r\\'\"][-あ" "'\\n\\t\\r\\\\\\'\\\"\\]\\[\\-\\u{3042}'", ELit "x" "\"x\""])
    , testCase "character classes" $
        exprs "[a-z_\\-0-9] [-a] [a-]" >>= (@?= [EClass [('a', 'z'), ('_', '_'), ('-', '-'), ('0', '9')] "[a-z_\\-0-9]", EClass [('-', '-'), ('a', 'a')] "[-a]", EClass [('a', 'a'), ('-', '-')] "[a-]"])
    , testCase "bindings" $ do
        g <- parseOk "%module M\nA :: Int\nA <- x:B 'c' y:$'d' { 1 }\nB :: Int\nB <- 'b' { 1 }\n"
        map itemBind (altItems (firstAlt g)) @?= [Just "x", Nothing, Just "y"]
    , testCase "actions with braces in strings and characters" $ do
        g <- parseOk "%module M\nA :: String\nA <- 'a' { \"}{\" ++ ['}'] ++ f' }\n"
        fmap unLoc (altAction (firstAlt g)) @?= Just " \"}{\" ++ ['}'] ++ f' "
    , testCase "action location is just after the brace" $ do
        g <- parseOk "%module M\nA :: ()\nA <- 'a'   { () }\n"
        fmap locOf (altAction (firstAlt g)) @?= Just (Loc 3 13)
    , testCase "A(x) is a call, A (x) is a sequence" $ do
        es1 <- exprs "B(1 + f (2, 3), x)"
        case es1 of
          [ERef _ "B" [a, b]] -> (unLoc a, unLoc b) @?= ("1 + f (2, 3)", "x")
          _ -> assertFailure (show es1)
        es2 <- exprs "B ('x')"
        case es2 of
          [ERef _ "B" [], EGroup [[Item _ Nothing (ELit "x" "'x'")]]] -> pure ()
          _ -> assertFailure (show es2)
    , testCase "rule parameters" $ do
        g <- parseOk "%module M\nA :: ()\nA <- B(1, 'x')\nB(n :: Int, c :: Char) :: ()\nB <- 'b' { () }\n"
        case grammarRules g of
          [_, b] -> [(paramName p, unLoc (paramType p)) | p <- ruleParams b] @?= [("n", "Int"), ("c", "Char")]
          rs -> assertFailure (show rs)
    , testCase "semantic predicates" $
        exprs "&{ n > 0 } !{ odd n }" >>= \es -> case es of
          [EPred True a, EPred False b] -> (unLoc a, unLoc b) @?= (" n > 0 ", " odd n ")
          _ -> assertFailure (show es)
    , testCase "a rule ends where the next declaration starts" $ do
        g <- parseOk "%module M\nA :: ()\nA <- B\n  C\nB :: ()\nB <- 'b' { () }\nC :: ()\nC <- 'c' { () }\n"
        map ruleName (grammarRules g) @?= ["A", "B", "C"]
        length (altItems (firstAlt g)) @?= 2
    , testCase "unknown directive" $ errorsOf "%module M\n%bogus\nA :: ()\nA <- 'a' { () }\n" @?= [(2, 1)]
    , testCase "missing %module" $ errorsOf "A :: ()\nA <- 'a' { () }\n" @?= [(1, 1)]
    , testCase "unknown escape" $ errorsOf "%module M\nA :: ()\nA <- '\\q' { () }\n" @?= [(3, 7)]
    , testCase "unterminated literal" $ errorsOf "%module M\nA :: ()\nA <- 'abc\n" @?= [(3, 10)]
    , testCase "action inside a group" $ errorsOf "%module M\nA :: ()\nA <- ('a' { () })\n" @?= [(3, 11)]
    ]
  where
    exprs' = map itemExpr . altItems . firstAlt

checkTests :: TestTree
checkTests =
  testGroup
    "static checks"
    [ testCase "undefined rule" $ errorsOf "%module M\nA :: ()\nA <- B { () }\n" @?= [(3, 6)]
    , testCase "unreachable rule" $ errorsOf "%module M\nA :: ()\nA <- 'a' { () }\nB :: ()\nB <- 'b' { () }\n" @?= [(5, 1)]
    , testCase "entries make rules reachable" $
        errorsOf "%module M\n%entry B\nA :: ()\nA <- 'a' { () }\nB :: ()\nB <- 'b' { () }\n" @?= []
    , testCase "repetition of a nullable expression" $ errorsOf "%module M\nA :: ()\nA <- 'a'? * { () }\n" @?= [(3, 6)]
    , testCase "repetition of a nullable rule" $
        errorsOf "%module M\nA :: ()\nA <- B+ { () }\nB :: ()\nB <- 'b'* { () }\n" @?= [(3, 6)]
    , testCase "binding an expression without a value" $ errorsOf "%module M\nA :: ()\nA <- c:[a-z] { () }\n" @?= [(3, 6)]
    , testCase "duplicate binding" $
        errorsOf "%module M\nA :: ()\nA <- x:$'a' x:$'b' { () }\n" @?= [(3, 13)]
    , testCase "reserved binding name" $ errorsOf "%module M\nA :: ()\nA <- _x:$'a' { () }\n" @?= [(3, 6)]
    , testCase "omitted action with no value" $ errorsOf "%module M\nA :: ()\nA <- 'unit'\n" @?= [(3, 6)]
    , testCase "omitted action with two values" $
        errorsOf "%module M\nA :: ()\nA <- $'a' $'b'\n" @?= [(3, 6)]
    , testCase "rule without a type annotation" $ errorsOf "%module M\nA <- 'a'\n" @?= [(2, 1)]
    , testCase "calling a rule without parameters" $
        messagesOf "%module M\nA :: ()\nA <- B(1)\nB :: ()\nB <- 'b' { () }\n" @?= ["rule B takes no arguments"]
    , testCase "wrong number of arguments" $
        errorsOf "%module M\nA :: ()\nA <- B\nB(n :: Int) :: ()\nB <- 'b' { () }\n" @?= [(3, 6)]
    , testCase "parameterised rule in left recursion" $
        errorsOf "%module M\nA :: ()\nA <- B(1)\nB(n :: Int) :: ()\nB <- B(n) 'b' { () } / 'b' { () }\n" @?= [(5, 1)]
    , testCase "an entry rule cannot take parameters" $
        errorsOf "%module M\n%entry B\nA :: ()\nA <- 'a' { () }\nB(n :: Int) :: ()\nB <- 'b' { () }\n" @?= [(2, 1)]
    , testCase "%language takes extension names" $
        errorsOf "%module M\n%language OverloadedStrings, overloaded\nA :: ()\nA <- 'a' { () }\n" @?= [(2, 30)]
    , testCase "%language RebindableSyntax is rejected" $
        errorsOf "%module M\n%language RebindableSyntax\nA :: ()\nA <- 'a' { () }\n" @?= [(2, 11)]
    , testCase "%nomemo on a left-recursive rule" $
        errorsOf "%module M\n%nomemo A\nA :: ()\nA <- A 'a' { () } / 'a' { () }\n" @?= [(2, 1)]
    , testCase "%token requires %syntax" $
        errorsOf "%module M\n%token A\nA :: ()\nA <- 'a' { () }\n" @?= [(2, 1)]
    , testCase "%syntax takes no argument" $
        errorsOf "%module M\n%syntax yes\nA :: ()\nA <- 'a' { () }\n" @?= [(2, 1)]
    , testCase "%trivia must name a %token rule" $
        errorsOf "%module M\n%syntax\n%trivia A\nA :: ()\nA <- 'a' { () }\n" @?= [(3, 1)]
    , testCase "a rule cannot be both %token and %inline" $
        errorsOf "%module M\n%syntax\n%token B\n%inline B\nA :: ()\nA <- B { () }\nB :: ()\nB <- 'b' { () }\n" @?= [(4, 1)]
    , testCase "an entry rule cannot be %inline" $
        errorsOf "%module M\n%syntax\n%inline A\nA :: ()\nA <- 'a' { () }\n" @?= [(3, 1)]
    , testCase "%recover expects a label and a rule" $
        errorsOf "%module M\n%recover onlyone\nA :: ()\nA <- 'a' ^onlyone { () }\n" @?= [(2, 1)]
    , testCase "a recovery rule cannot take parameters" $
        errorsOf "%module M\n%recover l R\nA :: ()\nA <- 'a' ^l { () }\nR(n :: Int) :: ()\nR <- 'r' { () }\n" @?= [(2, 10)]
    , testCase "a label has at most one recovery rule" $
        errorsOf "%module M\n%recover l R\n%recover l S\nA :: ()\nA <- 'a' ^l { () }\nR :: ()\nR <- 'r' { () }\nS :: ()\nS <- 's' { () }\n" @?= [(3, 10)]
    , testCase "a recovered label must appear in the grammar" $
        errorsOf "%module M\n%recover l R\nA :: ()\nA <- 'a' { () }\nR :: ()\nR <- 'r' { () }\n" @?= [(2, 10)]
    , testCase "recovery rules are reachable" $
        errorsOf "%module M\n%recover l R\nA :: ()\nA <- 'a' ^l { () }\nR :: ()\nR <- 'r' { () }\n" @?= []
    , testCase "reserved names in verbatim code" $
        errorsOf "%module M\n%{\npeg'x = 1\ndata Peg'T = T\nimport qualified Data.Map as PegRt\n}%\nA :: ()\nA <- 'a' { () }\n" @?= [(3, 1), (4, 1), (5, 1)]
    ]

analysisTests :: TestTree
analysisTests =
  testGroup
    "analysis"
    [ testCase "left recursion: direct, indirect and hidden" $ do
        g <-
          parseOk $
            T.unlines
              [ "%module M"
              , "%entry H"
              , "E :: ()"
              , "E <- E '+' 'n' { () } / L { () }"
              , "L :: ()"
              , "L <- P '.x' { () } / 'x' { () }"
              , "P :: ()"
              , "P <- P '(n)' { () } / L { () }"
              , "H :: ()"
              , "H <- '-'? H 'h' { () } / N { () }"
              , "N :: ()"
              , "N <- 'n' { () }"
              ]
        fmap analysisLeftRecursive (either (Left . show) Right (check g)) @?= Right (S.fromList ["E", "H", "L", "P"])
    , testCase "nullable rules" $ do
        g <- parseOk "%module M\nA :: ()\nA <- B C { () }\nB :: ()\nB <- 'b'? { () }\nC :: ()\nC <- &'c' { () }\n"
        fmap analysisNullable (either (Left . show) Right (check g)) @?= Right (S.fromList ["A", "B", "C"])
    , testCase "lookahead counts as a left call" $ do
        g <- parseOk "%module M\nA :: ()\nA <- !A 'a' { () }\n"
        fmap analysisLeftRecursive (either (Left . show) Right (check g)) @?= Right (S.fromList ["A"])
    ]
