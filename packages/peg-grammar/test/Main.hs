{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (filterM)
import qualified Data.ByteString.Lazy as BL
import Data.List (sort)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Check
import Peg.Grammar.Parser
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Format (formatTests)
import Labels (labelTests)
import Lint (lintTests)
import Shard (Shard, shardTests, sharded)
import Data.Proxy (Proxy (..))
import Test.Tasty.Options (OptionDescription (Option))
import Ranges (rangeTests)
import Recovery (recoveryTests)
import TemplateParams (templateParamTests)
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeExtension, (</>))
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit

main :: IO ()
main = do
  files <- grammarFiles
  missing <- filterM (fmap not . doesDirectoryExist) grammarDirectories
  -- The editor grammars are missing in a source tarball.
  editors <- doesDirectoryExist "../../editors/test"
  -- --shard runs a part of the tests, for the jobs of CI (ADR 0042).
  defaultMainWithIngredients (includingOptions [Option (Proxy :: Proxy Shard)] : defaultIngredients) . sharded $
    testGroup
      "peg-grammar"
      [ notationTests
      , checkTests
      , unitValueTests
      , templateTests
      , templateParamTests
      , analysisTests
      , repositoryGrammarTests files
      , errorReportTests
      , labelTests files
      , testGroup
          "type names of the syntax tree (ADR 0053)"
          [ testCase "a type name from a rule name" $
              map syntaxTypeName ["expr", "Expr", "数式", "_項", "\196", "\453"] @?= ["ExprSyntax", "ExprSyntax", "Rule'数式Syntax", "Rule'_項Syntax", "\196Syntax", "\452Syntax"]
          , testCase "rules with the same type name are an error with %syntax" $ do
              let two a b = "%module M\n%syntax\nS :: ()\nS <- " <> a <> " " <> b <> " { () }\n" <> a <> " :: ()\n" <> a <> " <- 'a' { () }\n" <> b <> " :: ()\n" <> b <> " <- 'b' { () }\n"
              checkErrorsAt (two "expr" "Expr") @?= [(8, 1, "the rules expr and Expr have the same type name ExprSyntax in the syntax tree; rename one of them")]
              checkErrorsAt (two "数式" "Rule'数式") @?= [(8, 1, "the rules 数式 and Rule'数式 have the same type name Rule'数式Syntax in the syntax tree; rename one of them")]
              checkErrorsAt (T.replace "%syntax\n" "" (two "expr" "Expr")) @?= []
          ]
      , testCase "a grammar with neither templates nor template calls is the same after expansion (ADR 0052)" $ do
          srcs <- mapM TIO.readFile files
          let plain = [g | Right g <- map parseGrammar srcs, not (any (not . null . ruleTemplateParams) (grammarRules g))]
          assertBool "grammars without templates" (not (null plain))
          [g | g <- plain, expandTemplates g /= Right g, not (hasTemplateCall g)] @?= []
      , formatTests files
      , lintTests files
      , shardTests
      , recoveryTests files
      , documentExampleTests
      , testGroup "editor grammars" [if editors then rangeTests files else testCaseInfo "the ranges for the editor grammars (ADR 0034)" (pure "skipped: ../../editors/test is not in a source archive")]
      , testCaseInfo "the grammars of the repository" (pure (unlines' [ "skipped: " <> d <> " is not in a source archive" | d <- missing ]))
      ]

-- Every grammar in the repository. Directories outside this package are
-- missing when the tests run from a source tarball, and are skipped.
grammarFiles :: IO [FilePath]
grammarFiles = concat <$> mapM pegsIn grammarDirectories
  where
    pegsIn d = do
      exists <- doesDirectoryExist d
      if exists
        then map (d </>) . filter ((== ".hpeg") . takeExtension) <$> listDirectory d
        else pure []

grammarDirectories :: [FilePath]
grammarDirectories =
  [ "grammar"
  , "../peg-codegen/test/fixtures"
  , "../../conformance/json"
  , "../../conformance/bench"
  , "../../conformance/commonmark"
  , "../../conformance/commonmark/v1"
  , "../../conformance/lua"
  , "../../conformance/toml"
  ]

-- Lines without a newline at the end, for the information of a test.
unlines' :: [String] -> String
unlines' = foldr (\l r -> if null r then l else l <> "\n" <> r) ""

-- Every grammar of the repository and a set of snippets are accepted, and
-- the invalid snippets rejected. These were the inputs of the migration
-- test from the hand-written parser (ADR 0015, ADR 0027).
repositoryGrammarTests :: [FilePath] -> TestTree
repositoryGrammarTests files =
  testGroup
    "repository grammars and snippets"
    ( [ testCase f $ do
          src <- TIO.readFile f
          assertBool ("rejected: " <> show (parseGrammar src)) (not (isLeft (parseGrammar src)))
      | f <- files
      ]
        ++ [ testCase ("snippet " <> show i) (assertBool (show (parseGrammar src)) (not (isLeft (parseGrammar src))))
           | (i, src) <- zip [1 :: Int ..] validSnippets
           ]
        ++ [ testCase ("rejected snippet " <> show i) (assertBool "should reject" (isLeft (parseGrammar src)))
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

-- ADR 0027: inputs that made the hand-written parser report each of its
-- messages, with a name for each.
errorSnippets :: [(Text, Text)]
errorSnippets =
  [ ("no rule at top", m <> "@ A :: Int\n")
  , ("directive without name", m <> "% x\nA :: Int\nA <- 'a' { 1 }\n")
  , ("unterminated verbatim", m <> "%{ import X\nA :: Int\nA <- 'a' { 1 }\n")
  , ("missing type", m <> "A :: \nA <- 'a' { 1 }\n")
  , ("parameters on a definition", m <> "A(x :: Int) :: Int\nA(x :: Int) <- 'a' { 1 }\n")
  , ("neither :: nor <-", m <> "A = 'a'\n")
  , ("parameter without a type", m <> "A(x) :: Int\nA <- 'a' { 1 }\n")
  , ("parameter with an empty type", m <> "A(x :: ) :: Int\nA <- 'a' { 1 }\n")
  , ("empty argument", m <> "A :: Int\nA <- B() { 1 }\n")
  , ("empty argument after a comma", m <> "A :: Int\nA <- B(1, ) { 1 }\n")
  , ("no expression after /", m <> "A :: Int\nA <- 'a' / ) { 1 }\n")
  , ("action in a group", m <> "A :: Int\nA <- ( 'a' { 1 } ) { 1 }\n")
  , ("unclosed group", m <> "A :: Int\nA <- ( 'a'\n")
  , ("unterminated literal", m <> "A :: Int\nA <- 'a { 1 }\n")
  , ("unterminated literal at the end", m <> "A :: Int\nA <- \"a")
  , ("empty range", m <> "A :: Int\nA <- [b-a] { 1 }\n")
  , ("empty class", m <> "A :: Int\nA <- [] { 1 }\n")
  , ("unterminated class", m <> "A :: Int\nA <- [a-z { 1 }\n")
  , ("unterminated class at the end", m <> "A :: Int\nA <- [a")
  , ("\\u escape out of range", m <> "A :: Int\nA <- '\\u{110000}' { 1 }\n")
  , ("\\u escape without a brace", m <> "A :: Int\nA <- '\\u41' { 1 }\n")
  , ("\\u escape not closed", m <> "A :: Int\nA <- '\\u{41' { 1 }\n")
  , ("unknown escape", m <> "A :: Int\nA <- '\\q' { 1 }\n")
  , ("unknown escape in a class", m <> "A :: Int\nA <- [\\q] { 1 }\n")
  , ("escape at the end", m <> "A :: Int\nA <- '\\")
  , ("unterminated action", m <> "A :: Int\nA <- 'a' { 1 \n")
  , ("unbalanced bracket in an action", m <> "A :: Int\nA <- 'a' { f) }\n")
  , ("unterminated string in an action", m <> "A :: Int\nA <- 'a' { \"x }\n")
  , ("unterminated character in an action", m <> "A :: Int\nA <- 'a' { '\\x }\n")
  , ("unterminated predicate", m <> "A :: Int\nA <- &{ True 'a' { 1 }\n")
  , ("unterminated argument", m <> "A :: Int\nA <- B(1 { 1 }\n")
  , ("label without a name", m <> "A :: Int\nA <- 'a' ^ { 1 }\n")
  , ("binding without an expression", m <> "A :: Int\nA <- x: { 1 }\n")
  , ("capture without an expression", m <> "A :: Int\nA <- $ { 1 }\n")
  , ("lookahead without an expression", m <> "A :: Int\nA <- & / 'a' { 1 }\n")
  ]
  where
    m = "%module M\n"

-- The first diagnostic, as line:column: message.
report :: Either [Diagnostic] Grammar -> Text
report = \case
  Left (Diagnostic (Loc l c) msg : _) -> T.pack (show l) <> ":" <> T.pack (show c) <> ": " <> msg
  Left [] -> "no diagnostic"
  Right _ -> "accepted"

-- The golden file holds the reports of the hand-written parser, which the
-- self-hosted parser reproduces (ADR 0027), except on these snippets:
--
-- - parameters on a definition: the hand-written parser never reported its
--   message there. Its repetition ended at a failure at the start of a
--   declaration, and the top level reported a generic message. The
--   self-hosted parser reports the specific message at '<-'.
-- - directive without name, empty class: the same message at the position
--   before. A predicate or a negative lookahead adds nothing to the
--   farthest position (ADR 0005), which labels cannot move (ADR 0021).
-- - parameter without a type, parameter with an empty type, empty range,
--   \u escape out of range: the same message at the end of the construct
--   instead of its start, since it is checked after it is read.
-- - unknown escape, unknown escape in a class: the same message one column
--   later, after the backslash, where the label is thrown.

errorReportTests :: TestTree
errorReportTests =
  testGroup
    "error reports (ADR 0027)"
    [ goldenVsString "the reports of the parser" "test/golden/error-reports.txt" $
        pure . BL.fromStrict . TE.encodeUtf8 . T.unlines $
          [n <> "\t" <> report (parseGrammar src) | (n, src) <- errorSnippets]
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
    , -- After the backslash, where the label is thrown (ADR 0027)
      testCase "unknown escape" $ errorsOf "%module M\nA :: ()\nA <- '\\q' { () }\n" @?= [(3, 8)]
    , testCase "unterminated literal" $ errorsOf "%module M\nA :: ()\nA <- 'abc\n" @?= [(3, 10)]
    , testCase "action inside a group" $ errorsOf "%module M\nA :: ()\nA <- ('a' { () })\n" @?= [(3, 11)]
    ]
  where
    exprs' = map itemExpr . altItems . firstAlt

-- ADR 0030: unit values of unbound items are not counted.
unitValueTests :: TestTree
unitValueTests =
  testGroup
    "unit values (ADR 0030)"
    [ testCase "a group with a unit rule has the value of the other item" $
        errorsOf (g "A :: [Int]\nA <- n:N ns:(',' Sp N)* { n : ns }") @?= []
    , testCase "a repeated unit rule is not counted" $
        errorsOf (g "A :: [Int]\nA <- n:N ns:(',' Sp* N)* { n : ns }") @?= []
    , testCase "an optional unit rule is not counted" $
        errorsOf (g "A :: Int\nA <- Sp? N") @?= []
    , testCase "an alternative without an action passes the value through" $
        errorsOf (g "A :: Int\nA <- Sp N Sp") @?= []
    , testCase "a single unit value is still passed through" $
        errorsOf (g "A :: ()\nA <- Sp") @?= []
    , testCase "two unit values without other values are two values" $
        messagesOf (g "A :: ()\nA <- Sp Sp") @?= ["an alternative without an action must have exactly one element with a value, but it has 2"]
    , testCase "a bound unit value is counted" $
        messagesOf (g "A :: Int\nA <- u:Sp N") @?= ["an alternative without an action must have exactly one element with a value, but it has 2"]
    , testCase "two values other than unit are an error" $
        messagesOf (g "A :: Int\nA <- N N") @?= ["an alternative without an action must have exactly one element with a value, but it has 2"]
    , testCase "a type synonym of () is not unit" $
        messagesOf (g "A :: Int\nA <- W N\nW :: Unit\nW <- ' ' { () }") @?= ["an alternative without an action must have exactly one element with a value, but it has 2"]
    , testCase "spaces in the type () are allowed" $
        errorsOf (g "A :: Int\nA <- V N\nV :: ( )\nV <- ' ' { () }") @?= []
    ]
  where
    g body = "%module M\n" <> body <> "\nSp :: ()\nSp <- ' '+ { () }\nN :: Int\nN <- [0-9] { 0 }\n%entry Sp\n%entry N\n"

-- ADR 0031: rule templates.
templateTests :: TestTree
templateTests =
  testGroup
    "rule templates (ADR 0031)"
    [ testCase "parse a template and its calls" $ do
        g <- parseOk (t "S :: [Int]\nS <- List<N, ','>")
        [ruleTemplateParams r | r <- grammarRules g, ruleName r == "List"] @?= [[TemplateParam "p" (Just "a"), TemplateParam "sep" Nothing]]
        [map itemExpr (altItems a) | r <- grammarRules g, ruleName r == "S", a <- ruleAlts r] @?= [[ETemplate (Loc 10 6) "List" [ERef (Loc 10 11) "N" [], ELit "," "','"] []]]
    , testCase "the same arguments make one instance, others another" $ do
        g <- expanded (t "S :: ([Int], [Int], [Int])\nS <- a:List<N, ','> b:List<N, ','> c:List<N, ';'> { (a, b, c) }")
        sort [ruleName r | r <- grammarRules g] @?= ["List'0", "List'1", "N", "S", "Sp"]
    , testCase "the type variable is replaced by the argument's type" $ do
        g <- expanded (t "S :: [Int]\nS <- List<N, ','>")
        [unLoc (ruleType r) | r <- grammarRules g, ruleName r == "List'0"] @?= ["[(Int)]"]
    , testCase "a capture argument has type Text" $ do
        g <- expanded (t "S :: [Text]\nS <- List<$[a-z]+, ','>")
        [unLoc (ruleType r) | r <- grammarRules g, ruleName r == "List'0"] @?= ["[(PegRt.Text)]"]
    , testCase "an untyped argument's value is discarded" $ do
        g <- expanded (t "S :: [Int]\nS <- List<N, N>")
        [map itemExpr (altItems a) | r <- grammarRules g, ruleName r == "List'0", a <- ruleAlts r]
          @?= [[ERef (Loc 10 11) "N" [], EStar (EGroup [[Item (Loc 4 25) Nothing (EDiscard (ERef (Loc 10 14) "N" [])), Item (Loc 4 29) Nothing (ERef (Loc 4 29) "Sp" []), Item (Loc 4 32) Nothing (ERef (Loc 10 11) "N" [])]])]]
        checkErrors (t "S :: [Int]\nS <- List<N, N>") @?= []
    , testCase "templates calling templates" $
        checkErrors (t "S :: [[Int]]\nS <- List<List<N, ','>, ';'>") @?= []
    , testCase "an untyped expression for a typed parameter" $
        checkErrors (t "S :: [Int]\nS <- List<'x', ','>") @?= ["the argument for p must be a rule, a capture or a template call, since its value is used"]
    , testCase "the number of arguments" $
        checkErrors (t "S :: [Int]\nS <- List<N>") @?= ["the template List expects 2 argument(s), but got 1"]
    , testCase "a template without arguments" $
        checkErrors (t "S :: [Int]\nS <- List") @?= ["the template List needs arguments: List<...>"]
    , testCase "a call of a rule that is not a template" $
        checkErrors (t "S :: Int\nS <- N<','>") @?= ["rule N is not a template"]
    , testCase "a template call in a grammar without templates (ADR 0052)" $
        expansionErrors "%module M\nA :: ()\nA <- B<'x'> B { () }\nB :: ()\nB <- 'b' { () }\n" @?= [(3, 6, "rule B is not a template")]
    , testCase "a template call of a missing rule in a grammar without templates (ADR 0052)" $
        expansionErrors "%module M\nA :: ()\nA <- 'a' X<'x'> { () }\n" @?= [(3, 10, "rule X is not a template")]
    , testCase "a template named in %entry" $
        checkErrors (t "%entry List\nS :: [Int]\nS <- List<N, ','>") @?= ["the template List cannot be named in %entry"]
    , testCase "the parameters of the definition and the annotation differ" $
        checkErrors "%module M\nS :: ()\nS <- T<'a'>\nT<x> :: ()\nT<y> <- x { () }\n" @?= ["the template parameters of the definition of T do not match its type annotation"]
    , testCase "an expansion that does not end" $
        fmap (T.isInfixOf "does not end") (checkErrors "%module M\nS :: ()\nS <- T<'a'>\nT<x> :: ()\nT<x> <- x T<(x x)> { () } / x { () }\n") @?= [True]
    , testCase "an error in a template is reported once, with the call that expanded it" $
        checkErrors (t "S :: ([Int], [Int])\nS <- a:List<N, ','> b:List<N, ';'> { (a, b) }\nBad<x> :: ()\nBad<x> <- x Missing { () }\nU :: ()\nU <- Bad<'a'> Bad<'b'> { () }\n%entry U")
          @?= ["undefined rule Missing (in the template Bad, expanded at 14:6)"]
    ]
  where
    t body =
      "%module M\n%start S\nList<p :: a, sep> :: [a]\nList<p, sep> <- x:p xs:(sep Sp p)* { x : xs }\nN :: Int\nN <- [0-9] { 0 }\nSp :: ()\nSp <- ' '* { () }\n" <> body <> "\n"
    expanded src = case parseGrammar src >>= expandTemplates of
      Right g -> pure g
      Left ds -> assertFailure (show ds) >> error "unreachable"
    checkErrors src = case parseGrammar src of
      Left ds -> map diagMessage ds
      Right g0 -> either (map diagMessage . templateNotes g0) (const []) (expandTemplates g0 >>= check)

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

-- Every complete grammar in the documents (a code block that starts with
-- %module) parses and passes the checks (ADR 0046). Fragments are not
-- checked.
documentExampleTests :: TestTree
documentExampleTests =
  testGroup
    "the complete grammars of the documents (ADR 0046)"
    [ testCaseInfo doc $ do
        exists <- doesDirectoryExist "../../docs"
        if not exists
          then pure ("skipped: ../../" <> doc <> " is not in a source archive")
          else do
            text <- TIO.readFile ("../../" <> doc)
            let examples = completeGrammars text
                bad = [(n, ds) | (n, src) <- examples, Left ds <- [parseGrammar src >>= \g -> either (Left . templateNotes g) Right (expandTemplates g >>= \g' -> g' <$ check g')]]
            assertBool "no complete grammar" (not (null examples))
            take 1 bad @?= []
            pure (show (length examples) <> " grammars")
    | doc <- ["docs/syntax.md", "README.md", "README.ja.md"]
    ]

-- The code blocks that start with %module, with the line of their start.
completeGrammars :: Text -> [(Int, Text)]
completeGrammars = go . zip [1 ..] . T.lines
  where
    go ls = case dropWhile (not . isFence . snd) ls of
      [] -> []
      (_, _) : rest ->
        let (body, rest') = break (isFence . snd) rest
         in [(n, T.unlines (map snd body)) | (n, l) : _ <- [body], "%module" `T.isPrefixOf` l] ++ go (drop 1 rest')
    isFence = T.isPrefixOf "```"

-- The errors of expanding the templates of a grammar, as (line, column,
-- message).
expansionErrors :: Text -> [(Int, Int, Text)]
expansionErrors src = case parseGrammar src >>= expandTemplates of
  Left ds -> [(locLine l, locColumn l, m) | Diagnostic l m <- ds]
  Right _ -> []

-- Whether a grammar calls a template anywhere.
hasTemplateCall :: Grammar -> Bool
hasTemplateCall g = any (any (any (expr . itemExpr) . altItems) . ruleAlts) (grammarRules g)
  where
    expr = \case
      ETemplate {} -> True
      EGroup alts -> any (any (expr . itemExpr)) alts
      EStar x -> expr x
      EPlus x -> expr x
      EOpt x -> expr x
      EAnd x -> expr x
      ENot x -> expr x
      ECapture x -> expr x
      ELabel _ x _ -> expr x
      EDiscard x -> expr x
      _ -> False

-- The errors of parsing and checking a grammar, as (line, column, message).
checkErrorsAt :: Text -> [(Int, Int, Text)]
checkErrorsAt src = case parseGrammar src >>= check of
  Left ds -> [(locLine l, locColumn l, m) | Diagnostic l m <- ds]
  Right _ -> []
