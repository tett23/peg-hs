{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Data.Version (showVersion)
import qualified Fixture.Arith as Arith
import qualified Fixture.Calc as Calc
import qualified Fixture.Discard as Discard
import qualified Fixture.DiscardSyntax as DiscardSyntax
import qualified Fixture.Extensions as Extensions
import qualified Fixture.Indent as Indent
import qualified Fixture.Link as Link
import qualified Fixture.Located as Located
import qualified Fixture.Misc as Misc
import qualified Fixture.NoMemo as NoMemo
import qualified Fixture.Recover as Recover
import qualified Fixture.RecoverNoLabels as RecoverNoLabels
import qualified Fixture.Sum as Sum
import qualified Fixture.Syntax as Syntax
import qualified Fixture.Templates as Templates
import qualified Fixture.TemplatesSyntax as TemplatesSyntax
import qualified Fixture.Unicode as Unicode
import qualified Fixture.Units as Units
import qualified Fixture.UnitsSyntax as UnitsSyntax
import Peg.Codegen
import Peg.Grammar (Diagnostic (..), Loc (..))
import Peg.Grammar.Labels (stripLabelsAs)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Runtime
import Peg.Runtime.Internal (Config (..), Stats (..), defaultConfig)
import Peg.Runtime.Syntax
import Control.Monad (when)
import System.Directory (createDirectoryIfMissing, doesFileExist, getTemporaryDirectory)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Info (fullCompilerVersion)
import System.Process (readProcessWithExitCode)
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck (Gen, Property, choose, elements, forAll, listOf, oneof, sized, testProperty, (.&&.), (===), withNumTests)

main :: IO ()
main =
  defaultMain $
    testGroup
      "peg-codegen"
      [ regenerationTests
      , variantTests
      , goldenVsString "default options (Sum)" "test/golden/Sum.hs.golden" $
          generateFixture Options {optSourceName = "test/fixtures/Sum.peg", optOutputName = "test/golden/Sum.hs.golden", optDebugEntry = False} "Sum"
      , sumTests
      , arithTests
      , calcTests
      , miscTests
      , indentTests
      , linkTests
      , locatedTests
      , extensionTests
      , nomemoTests
      , syntaxTests
      , recoveryTests
      , testCase "Unicode rule and binding names (ADR 0020)" $ Unicode.parse "1＋20＋300" @?= Right 321
      , discardTests
      , testGroup
          "rule templates (ADR 0031)"
          [ testCase "values" $ Templates.parse templateInput @?= Right templateExpected
          , testCase "%syntax, typed entry" $ fmap show (TemplatesSyntax.parse templateInput) @?= Right (show templateExpected)
          , testCase "each instance has its own memo table" $ do
              let st = snd (Templates.peg'parseWith defaultConfig {cfgCount = True} templateInput)
                  instances = [r | r <- M.keys (statsEntriesByRule st), "'" `T.isInfixOf` r]
              assertBool (show instances) (length instances >= 5)
          , testCase "a template call makes no node, and the tree is lossless" $ do
              case TemplatesSyntax.parseSyntax templateInput of
                Left e -> assertFailure (show e)
                Right tree -> do
                  syntaxText tree @?= templateInput
                  let kinds = map TemplatesSyntax.nameOfSyntaxKind (descendantKinds tree)
                  assertBool (show kinds) (not (any ("'" `T.isInfixOf`) kinds))
          ]
      , testGroup
          "unit values are not counted (ADR 0030)"
          [ testCase "typed" $ Units.parse "1, 2,3;4; 5;  " @?= Right (Units.Result [1, 2, 3] 4 (Just 5) ())
          , testCase "%syntax, typed entry" $ fmap show (UnitsSyntax.parse "1, 2,3;4; 5;  ") @?= Right (show (UnitsSyntax.Result [1, 2, 3] 4 (Just 5) ()))
          , testCase "%syntax, lossless tree" $ fmap syntaxText (UnitsSyntax.parseSyntax "1;2;; ") @?= Right "1;2;; "
          ]
      , testGroup
          "values that are not used (ADR 0026)"
          [ testCase "typed" $ Discard.parse unusedInput @?= Right unusedExpected
          , testCase "%syntax, typed entry" $ DiscardSyntax.parse unusedInput @?= Right unusedExpected
          , testCase "%syntax, lossless tree" $ fmap syntaxText (DiscardSyntax.parseSyntax unusedInput) @?= Right unusedInput
          ]
      , generatorErrorTests
      , compileTests
      ]

fixtures :: [String]
fixtures = ["Arith", "Calc", "Discard", "DiscardSyntax", "Extensions", "Indent", "Link", "Located", "Misc", "NoMemo", "Recover", "Sum", "Syntax", "Templates", "TemplatesSyntax", "Unicode", "Units", "UnitsSyntax"]

fixtureOptions :: String -> Options
fixtureOptions n =
  Options
    { optSourceName = "test/fixtures/" <> n <> ".peg"
    , optOutputName = "test/generated/Fixture/" <> n <> ".hs"
    , optDebugEntry = True
    }

generateFixture :: Options -> String -> IO BL.ByteString
generateFixture opts n = do
  src <- TIO.readFile ("test/fixtures/" <> n <> ".peg")
  case generateFromSource opts src of
    Left ds -> assertFailure (show ds) >> pure ""
    Right code -> pure (BL.fromStrict (TE.encodeUtf8 code))

-- The committed generated modules must be exactly what the generator
-- produces now (ADR 0002, ADR 0010).
regenerationTests :: TestTree
regenerationTests =
  testGroup
    "committed fixtures are up to date"
    [ testCase n $ do
        expected <- BL.readFile (optOutputName (fixtureOptions n))
        actual <- generateFixture (fixtureOptions n) n
        assertBool ("regenerate with scripts/regen-fixtures.sh: " <> n) (actual == expected)
    | n <- fixtures
    ]

-- ADR 0024: discarding only the entries that depend on a growing seed gives
-- the same results, failures and syntax errors as discarding every entry
-- written during an iteration (ADR 0013).
discardTests :: TestTree
discardTests =
  testGroup
    "discarding only seed dependents (ADR 0024)"
    [ -- The value of Arith can overflow Int and fail to evaluate ("Negative
      -- exponent"), so only acceptance and the error are compared.
      same "Arith" "0123456789+-*^() " (\c -> either show (const "ok") . fst . Arith.peg'parseWith c)
    , same "Calc" "x(n).+-0123456789" (\c -> show . fst . Calc.peg'parseWith c)
    , same "Located" "0123456789+ " (\c -> show . fst . Located.peg'parseWith c)
    , same "Sum" "0123456789+" (\c -> show . fst . Sum.peg'parseWith c)
    , same "Syntax (typed)" "0123456789+-*() #\n" (\c -> show . fst . Syntax.peg'parseWith c)
    , same "Syntax (tree)" "0123456789+-*() #\n" (\c -> show . fst . Syntax.peg'parseSyntaxWith c)
    , same "Recover" "ab[] \n" (\c t -> let (v, e, _) = Recover.peg'parseRecoverWith c t in show (v, e))
    , same "Unicode" "0123456789＋" (\c -> show . fst . Unicode.peg'parseWith c)
    ]
  where
    same name alphabet run =
      testProperty name $
        forAll (T.pack <$> listOf (elements alphabet)) $ \t ->
          run defaultConfig t === run defaultConfig {cfgDiscardAll = True} t

unusedInput :: Text
unusedInput = "$12;$ab;&x1;!.;*1a2;?z;?;^42;"

unusedExpected :: [Text]
unusedExpected = ["12", "ab", "x1", "none", "many", "optional", "optional", "42"]

-- The self-hosted parser of the notation (ADR 0027), and the grammars
-- without labels used to test that the labels are safe (ADR 0028), are up
-- to date. The files of peg-grammar are missing in a source tarball.
variantTests :: TestTree
variantTests =
  testGroup
    "committed self-hosted parser and label-free variants are up to date"
    [ check "self-hosted parser" "../peg-grammar" "grammar/Peg.peg" "src/Peg/Grammar/SelfHosted.hs" Nothing
    , check "self-hosted parser with a syntax tree" "../peg-grammar" "grammar/PegSyntax.peg" "src/Peg/Grammar/SelfHostedSyntax.hs" Nothing
    , testCase "the syntax tree variant of the notation's grammar is derived from it" $ do
        exists <- doesFileExist "../peg-grammar/grammar/Peg.peg"
        when exists $ do
          src <- TIO.readFile "../peg-grammar/grammar/Peg.peg"
          extra <- TIO.readFile "../peg-grammar/grammar/SyntaxVariant.txt"
          variant <- TIO.readFile "../peg-grammar/grammar/PegSyntax.peg"
          assertBool "regenerate with scripts/regen-fixtures.sh: grammar/PegSyntax.peg" (syntaxVariant src extra == variant)
    , check "JSON parser of the language server" "../peg-lsp" "grammar/Json.peg" "src/Peg/Lsp/JsonParser.hs" Nothing
    , testCase "the JSON grammar of the language server is derived from the conformance one" $ do
        exists <- doesFileExist "../../conformance/json/Json.peg"
        when exists $ do
          src <- TIO.readFile "../../conformance/json/Json.peg"
          derived <- TIO.readFile "../peg-lsp/grammar/Json.peg"
          assertBool "regenerate with scripts/regen-fixtures.sh: packages/peg-lsp/grammar/Json.peg" (T.replace "%module Conformance.Json.Parser\n" "%module Peg.Lsp.JsonParser\n" src == derived)
    , check "self-hosted parser without labels" "../peg-grammar" "grammar/Peg.peg" "test/generated/SelfHostedNoLabels.hs" (Just "SelfHostedNoLabels")
    , check "Recover without labels" "." "test/fixtures/Recover.peg" "test/generated/Fixture/RecoverNoLabels.hs" (Just "Fixture.RecoverNoLabels")
    , testProperty "the Recover fixture accepts the same inputs without its labels" $
        withNumTests 3000 $ forAll (T.pack <$> listOf (elements "ab[] \n")) $ \t ->
          either (const False) (const True) (Recover.parse t) === either (const False) (const True) (RecoverNoLabels.parse t)
    ]
  where
    check name dir src out strip = testCase name $ do
      exists <- doesFileExist (dir </> src)
      when exists $ do
        grammarText <- TIO.readFile (dir </> src)
        committed <- BL.readFile (dir </> out)
        let opts = Options {optSourceName = src, optOutputName = out, optDebugEntry = False}
            code = case strip of
              Nothing -> generateFromSource opts grammarText
              Just m -> parseGrammar grammarText >>= generate opts . stripLabelsAs m
        case code of
          Left ds -> assertFailure (show ds)
          Right c -> assertBool ("regenerate with scripts/regen-fixtures.sh: " <> out) (BL.fromStrict (TE.encodeUtf8 c) == committed)

-- The notation's grammar with a lossless syntax tree and recovery, as
-- derived by scripts/regen-fixtures.sh (ADR 0032, ADR 0035).
syntaxVariant :: Text -> Text -> Text
syntaxVariant src extra = T.unlines (map line (T.lines src)) <> extra
  where
    line l
      | l == "%module Peg.Grammar.SelfHosted" = "%module Peg.Grammar.SelfHostedSyntax"
      | l == "TopItem <- t:TopOne Ws { t }" = "TopItem <- &. t:(TopOne ^topitem) Ws { t }"
      | otherwise = l

templateInput :: Text
templateInput = "lists 1, 2; 3 expr 1 + 2 + 3 vars a, b"

templateExpected :: ([[Int]], Templates.Expr, Templates.Expr)
templateExpected = ([[1, 2], [3]], Templates.Add (Templates.Add (Templates.Num 1) (Templates.Num 2)) (Templates.Num 3), Templates.Vars ["a", "b"])

descendantKinds :: SyntaxNode -> [SyntaxKind]
descendantKinds n = syntaxKind n : concatMap descendantKinds (syntaxChildren n)

flipE :: Either a b -> Either b a
flipE = either Right Left

rendered :: Either ParseError a -> Either Text a
rendered = either (Left . renderParseError) Right

sumTests :: TestTree
sumTests =
  testGroup
    "Sum"
    [ testCase "left associative sum" $ Sum.parse "1+2+3" @?= Right 6
    , testCase "error" $ fmap renderParseError (flipE (Sum.parse "1+")) @?= Right "1:3: expected [0-9]"
    ]

arithTests :: TestTree
arithTests =
  testGroup
    "Arith"
    [ testCase "precedence" $ Arith.parse "2*3+4" @?= Right 10
    , testCase "left associative subtraction" $ Arith.parse "10-3-2" @?= Right 5
    , testCase "right associative power" $ Arith.parse "2^3^2" @?= Right 512
    , testCase "parentheses" $ Arith.parse "2*(3+4)" @?= Right 14
    , testCase "%entry Term" $ Arith.parseTerm "2*3" @?= Right 6
    , testCase "%entry requires the whole input" $
        rendered (Arith.parseTerm "2+3") @?= Left "1:2: expected '*', '^', [0-9] or end of input"
    , testCase "the error example of syntax.md" $
        rendered (Arith.parse "1+*2") @?= Left "1:3: expected '(' or [0-9]"
    , testCase "memoisation does not change results or errors" $
        mapM_
          (\s -> fst (Arith.peg'parseWith defaultConfig {cfgMemo = False} s) @?= fst (Arith.peg'parseWith defaultConfig s))
          ["1+2*3", "(1+2", "2^^3", "", "1+2*(3+4)-5^2", "((((1))))"]
    ]

calcTests :: TestTree
calcTests =
  testGroup
    "Calc"
    [ testCase "indirect left recursion" $ Calc.parse "x(n)(n).x(n).x" @?= Right "x(n)(n).x(n).x"
    , testCase "hidden left recursion is left associative" $ Calc.parseH "1+2+3" @?= Right "((1+2)+3)"
    , testCase "hidden left recursion with a single digit" $ Calc.parseH "7" @?= Right "7"
    ]

miscTests :: TestTree
miscTests =
  testGroup
    "Misc"
    [ testCase "items" $
        Misc.parse "  foo_1 42 \"a\\\"b\" <ab12,_> あう \x1F600\n"
          @?= Right [Misc.Word "foo_1", Misc.Number 42, Misc.Quoted "a\\\"b", Misc.Pair "12" "_", Misc.Word "あう", Misc.Word "smile"]
    , testCase "trailing garbage" $
        fmap (S.toList . parseErrorExpected) (flipE (Misc.parse "foo !"))
          @?= Right
            [ ExpectedLiteral "\"\\u{1F600}\""
            , ExpectedLiteral "'\"'"
            , ExpectedLiteral "'<'"
            , ExpectedLiteral "'あ'"
            , ExpectedClass "[ \\t\\n]"
            , ExpectedClass "[0-9]"
            , ExpectedClass "[a-z]"
            ]
    , testCase "each rule body runs at most once per offset without left recursion" $ do
        let (r, st) = Misc.peg'parseWith defaultConfig {cfgCount = True} "foo 1 <a1,_> bar"
        assertBool "parse failed" (either (const False) (const True) r)
        assertBool "evaluated more than once" (all (<= 1) (M.elems (statsEvaluations st)))
        statsMemoEntries st @?= M.size (statsEvaluations st)
    ]

indentTests :: TestTree
indentTests =
  testGroup
    "Indent"
    [ testCase "nested by indentation, with a tab stop of 2" $
        Indent.parse "a\n  b\n\tc\n    d\ne\n"
          @?= Right [Indent.Node "a" [Indent.Node "b" [], Indent.Node "c" [Indent.Node "d" []]], Indent.Node "e" []]
    , testCase "odd indentation is rejected" $
        assertBool "should fail" (either (const True) (const False) (Indent.parse "a\n b\n"))
    , testCase "the same rule at the same offset with different arguments" $ do
        let (r, st) = Indent.peg'parseWith defaultConfig {cfgCount = True} "a\n  b\nc\n"
        r @?= Right [Indent.Node "a" [Indent.Node "b" []], Indent.Node "c" []]
        -- Node(0), Node(2) and Node(4) all start at the offset of "c".
        M.lookup ("Node", 6) (statsEvaluations st) @?= Just 3
    , testProperty "memoisation does not change results (arguments, predicates, columns)" indentInvariant
    ]

indentInvariant :: Property
indentInvariant =
  forAll (listOf (elements "ab \t\n\n")) $ \s ->
    let t = T.pack s
     in fst (Indent.peg'parseWith defaultConfig {cfgMemo = False} t) === fst (Indent.peg'parseWith defaultConfig t)

linkTests :: TestTree
linkTests =
  testGroup
    "Link"
    [ testCase "a defined link" $ Link.parse (S.fromList ["foo"]) "see [foo]" @?= Right ["see ", "foo"]
    , testCase "an undefined link" $ assertBool "should fail" (either (const True) (const False) (Link.parse (S.fromList ["foo"]) "[bar]"))
    ]

locatedTests :: TestTree
locatedTests =
  testCase "spans of alternatives" $
    Located.parse "1+22"
      @?= Right
        ( Located.Add
            (Span (Pos 0 1 1) (Pos 4 1 5))
            (Located.Lit (Span (Pos 0 1 1) (Pos 1 1 2)) 1)
            (Located.Lit (Span (Pos 2 1 3) (Pos 4 1 5)) 22)
        )

-- Errors reported by the generator --------------------------------------------

generatorErrors :: Text -> [(Int, Int, Text)]
generatorErrors src = case generateFromSource defaultOptions src of
  Left ds -> [(locLine l, locColumn l, m) | Diagnostic l m <- ds]
  Right _ -> []

generatorErrorTests :: TestTree
generatorErrorTests =
  testGroup
    "generator errors"
    [ testCase "%recover names an undefined rule" $
        map (\(l, c, _) -> (l, c)) (generatorErrors "%module M\n%recover oops Missing\nA :: ()\nA <- 'a' ^oops { () }\n") @?= [(2, 10)]
    , testCase "%nomemo on a left-recursive rule" $
        map (\(l, c, _) -> (l, c)) (generatorErrors "%module M\n%nomemo A\nA :: ()\nA <- A 'a' { () } / 'a' { () }\n") @?= [(2, 1)]
    , testCase "%language RebindableSyntax is rejected" $
        map (\(l, c, _) -> (l, c)) (generatorErrors "%module M\n%language LambdaCase, RebindableSyntax\nA :: ()\nA <- 'a' { () }\n") @?= [(2, 23)]
    ]

-- Compiling generated code with GHC ------------------------------------------

ghc :: FilePath
ghc = "ghc-" <> showVersion fullCompilerVersion

-- Generate a module from a grammar and type-check it with GHC, using the
-- runtime sources directly so that no package database is needed.
typecheck :: String -> Text -> IO (ExitCode, String)
typecheck name src = do
  tmp <- getTemporaryDirectory
  let dir = tmp </> "peg-codegen-test"
      opts = Options {optSourceName = name <> ".peg", optOutputName = name <> ".hs", optDebugEntry = False}
  createDirectoryIfMissing True dir
  case generateFromSource opts src of
    Left ds -> assertFailure (show ds) >> pure (ExitFailure 1, "")
    Right code -> do
      TIO.writeFile (dir </> name <> ".hs") code
      (ex, _, err) <-
        readProcessWithExitCode
          ghc
          ["-fno-code", "-i../peg-runtime/src", "-outputdir", dir </> "out", dir </> name <> ".hs"]
          ""
      pure (ex, err)

compileTests :: TestTree
compileTests =
  testGroup
    "compiling generated code"
    [ testCase "type errors in actions point at the grammar" $ do
        (ex, err) <-
          typecheck "Bad" $
            T.unlines
              [ "%module Bad"
              , ""
              , "A :: Int"
              , "A <- 'a' { 1 }"
              , "   / 'b'    { not True }"
              ]
        ex @?= ExitFailure 1
        assertBool ("error not reported at Bad.peg:5:15\n" <> err) ("Bad.peg:5:15" `T.isInfixOf` T.pack err)
    , testCase "type errors in rule types point at the grammar" $ do
        (_, err) <-
          typecheck "BadType" $
            T.unlines ["%module BadType", "", "A :: Intt", "A <- 'a' { 1 }"]
        assertBool ("error not reported at BadType.peg:3:6\n" <> err) ("BadType.peg:3:6" `T.isInfixOf` T.pack err)
    , testCase "argument types must be instances of Ord" $ do
        (ex, err) <-
          typecheck "NoOrd" $
            T.unlines
              [ "%module NoOrd"
              , "A :: Int"
              , "A <- B(id) { 1 }"
              , "B(f :: Int -> Int) :: ()"
              , "B <- 'b' { () }"
              ]
        ex @?= ExitFailure 1
        assertBool ("expected a missing Ord instance\n" <> err) ("Ord" `T.isInfixOf` T.pack err)
    , testCase "multi-line actions keep their layout" $ do
        (ex, err) <-
          typecheck "MultiLine" $
            T.unlines
              [ "%module MultiLine"
              , "A :: Int"
              , "A <- s:$'a'+ { case s of"
              , "                 _ -> 1"
              , "             }"
              ]
        assertEqual err ExitSuccess ex
    ]

-- ADR 0016 ---------------------------------------------------------------------

extensionTests :: TestTree
extensionTests =
  testGroup
    "%language (ADR 0016)"
    [ testCase "pragmas come before the module line, in order" $ do
        src <- TIO.readFile "test/fixtures/Extensions.peg"
        case generateFromSource (fixtureOptions "Extensions") src of
          Left ds -> assertFailure (show ds)
          Right gen -> do
            let ls = T.lines gen
                (before, _) = break (T.isPrefixOf "module ") ls
                pragmas = filter (T.isPrefixOf "{-# LANGUAGE") before
            pragmas
              @?= [ "{-# LANGUAGE " <> x <> " #-}"
                  | x <- ["OverloadedStrings", "OverloadedLists", "LambdaCase", "Strict", "StrictData", "NoImplicitPrelude"]
                  ]
            assertBool "no implicit Prelude import was added" (not (any (== "import Prelude") ls))
    , testCase "the same results as without extensions" $
        mapM_
          (\i -> (rendered (Extensions.parse i), rendered (Extensions.parseTerm i)) @?= (rendered (Arith.parse i), rendered (Arith.parseTerm i)))
          ["2*3+4", "10-3-2", "2^3^2", "2*(3+4)", "1+*2", "", "(1"]
    ]

-- ADR 0017 ---------------------------------------------------------------------

nomemoTests :: TestTree
nomemoTests =
  testGroup
    "%nomemo (ADR 0017)"
    [ testProperty "results and errors do not change" $
        forAll (listOf (elements "ab1 <,_>\"\\あう\n!")) $ \s ->
          let t = T.pack s in show (Misc.parse t) === show (NoMemo.parse t)
    , testCase "rules without memoisation leave no memo entries" $ do
        let (r, st) = NoMemo.peg'parseWith defaultConfig {cfgCount = True} "foo 1 <a1,_> bar"
        assertBool "parse failed" (either (const False) (const True) r)
        let byRule = M.filter (> 0) (statsEntriesByRule st)
        assertBool ("unexpected entries: " <> show byRule) (not (M.member "Spaces" byRule) && not (M.member "Key" byRule))
        assertBool "memoised rules still have entries" (M.member "Item" byRule)
    ]

-- ADR 0019 ---------------------------------------------------------------------

treeOf :: Text -> SyntaxNode
treeOf t = either (error . show) id (Syntax.parseSyntax t)

syntaxInputs :: [Text]
syntaxInputs =
  [ "1"
  , "1 + 2"
  , "1+2*3"
  , "1 + 2 * (3 # three\n - 4)"
  , "  1"
  , "(1"
  , "1 + # trailing"
  , "2 * 3 - 4 * 5 + 6"
  ]

syntaxTests :: TestTree
syntaxTests =
  testGroup
    "syntax trees (ADR 0019)"
    [ goldenVsString "debug display" "test/golden/Syntax.tree.golden" $
        pure . BL.fromStrict . TE.encodeUtf8 . T.concat $
          [ "# " <> t <> "\n" <> either (\e -> "error: " <> renderParseError e <> "\n") (debugTree Syntax.nameOfSyntaxKind) (Syntax.parseSyntax t)
          | t <- syntaxInputs
          ]
    , testCase "lossless: the text of the tree is the input" $
        mapM_ (\t -> fmap syntaxText (Syntax.parseSyntax t) @?= either Left (const (Right t)) (Syntax.parseSyntax t)) syntaxInputs
    , testProperty "lossless on generated expressions" $
        forAll genExpr $ \t -> fmap syntaxText (Syntax.parseSyntax t) === Right t
    , testCase "the typed and the tree entry points agree" $
        mapM_
          (\t -> (either (Left . renderParseError) (const (Right ())) (Syntax.parse t)) @?= either (Left . renderParseError) (const (Right ())) (Syntax.parseSyntax t))
          (syntaxInputs ++ ["", "+", "1 +", "1 2"])
    , testCase "%entry has a tree entry point" $
        fmap syntaxText (Syntax.parseSyntaxTerm "2 * 3") @?= Right "2 * 3"
    , testCase "memoisation does not change the tree" $
        mapM_
          ( \t ->
              fmap (debugTree Syntax.nameOfSyntaxKind) (fst (Syntax.peg'parseSyntaxWith defaultConfig {cfgMemo = False} t))
                @?= fmap (debugTree Syntax.nameOfSyntaxKind) (fst (Syntax.peg'parseSyntaxWith defaultConfig t))
          )
          syntaxInputs
    , testCase "typed accessors" $ do
        let root = treeOf "1 + 2 * 3"
        Just e <- pure (Syntax.castExprSyntax root)
        fmap (\(Syntax.ExprSyntax n) -> syntaxText n) (Syntax.exprL e) @?= Just "1"
        fmap (\(Syntax.TermSyntax n) -> syntaxText n) (Syntax.exprR e) @?= Just "2 * 3"
        map elementText (Syntax.exprOp e) @?= ["+"]
        Just (Syntax.TermSyntax t) <- pure (Syntax.exprR e)
        Just term <- pure (Syntax.castTermSyntax t)
        fmap (\(Syntax.FactorSyntax n) -> syntaxText n) (Syntax.termR term) @?= Just "3"
        Just (Syntax.FactorSyntax f) <- pure (Syntax.termR term)
        Just factor <- pure (Syntax.castFactorSyntax f)
        fmap tokenText (Syntax.factorN factor) @?= Just "3"
    , testCase "trivia are tokens of their own kind" $ do
        let root = treeOf "1 # c\n+ 2"
            kinds = [Syntax.nameOfSyntaxKind (tokenKind t) | t <- syntaxTokens root, Syntax.isTriviaSyntaxKind (tokenKind t)]
        kinds @?= ["Ws", "Comment", "Ws", "Ws"]
    , testCase "positions of nodes" $ do
        let root = treeOf "1 +\n2"
        syntaxPos root 4 @?= Pos 4 2 1
    ]
  where
    elementText (TokenElement t) = tokenText t
    elementText (NodeElement n) = syntaxText n

genExpr :: Gen Text
genExpr = T.pack <$> sized go
  where
    go n
      | n <= 1 = atom
      | otherwise =
          oneof
            [ atom
            , do a <- go (n `div` 2); o <- elements ["+", "-", "*"]; s1 <- sp; s2 <- sp; b <- go (n `div` 2); pure (a <> s1 <> o <> s2 <> b)
            , do s1 <- sp; s2 <- sp; a <- go (n `div` 2); pure ("(" <> s1 <> a <> s2 <> ")")
            ]
    atom = show <$> (choose (0, 999) :: Gen Int)
    sp = elements ["", " ", "  ", "\n", " # c\n", "\t"]

-- ADR 0021 ---------------------------------------------------------------------

errorRanges :: [SyntaxError] -> [(Maybe Text, (Int, Int))]
errorRanges = map (\e -> (syntaxErrorLabel e, syntaxErrorRange e))

errorNodes :: SyntaxNode -> [(Int, Int)]
errorNodes n = [syntaxRange n | syntaxKind n == errorKind] ++ concatMap errorNodes (syntaxChildren n)

recoveryTests :: TestTree
recoveryTests =
  testGroup
    "recovery (ADR 0021)"
    [ testCase "a valid document parses the same way in both modes" $ do
        let doc = "a [b c] d\n\ne [f]"
            expected = [Recover.Para [Recover.Plain "a ", Recover.Command "b" [Recover.Plain " c"], Recover.Plain " d"], Recover.Para [Recover.Plain "e ", Recover.Command "f" []]]
        Recover.parse doc @?= Right expected
        Recover.parseRecover doc @?= (Just expected, [])
        let (tree, errs) = Recover.parseSyntaxRecover doc
        (syntaxText tree, errs, errorNodes tree) @?= (doc, [], [])
    , testCase "without recovery the parse fails with the label" $
        fmap parseErrorLabel (flipE (Recover.parse "ok\n\n] broken")) @?= Right (Just "block")
    , testCase "a broken block becomes an error node; its neighbours are intact" $ do
        let doc = "good one\n\n] broken [x\n\ngood two"
            (v, errs) = Recover.parseRecover doc
        v @?= Just [Recover.Para [Recover.Plain "good one"], Recover.ErrorBlock, Recover.Para [Recover.Plain "good two"]]
        errorRanges errs @?= [(Just "block", (10, 21))]
        let (tree, _) = Recover.parseSyntaxRecover doc
        syntaxText tree @?= doc
        errorNodes tree @?= [(10, 21)]
    , testCase "an unclosed command is closed at the end of its paragraph" $ do
        let doc = "see [b unclosed\n\nnext"
            (v, errs) = Recover.parseRecover doc
        v @?= Just [Recover.Para [Recover.Plain "see ", Recover.Command "b" [Recover.Plain " unclosed"]], Recover.Para [Recover.Plain "next"]]
        errorRanges errs @?= [(Just "close", (15, 15))]
        let (tree, _) = Recover.parseSyntaxRecover doc
        errorNodes tree @?= [(15, 15)]
    , testCase "a missing command name is inserted" $ do
        let (v, errs) = Recover.parseRecover "x [ y]"
        v @?= Just [Recover.Para [Recover.Plain "x ", Recover.Command "?" [Recover.Plain " y"]]]
        errorRanges errs @?= [(Just "name", (3, 3))]
    , testProperty "every input gives a lossless tree" $
        forAll (T.pack <$> listOf (elements "ab []\n\nx\x3042")) $ \t ->
          let (tree, errs) = Recover.parseSyntaxRecover t
           in syntaxText tree === t .&&. all (\e -> fst (syntaxErrorRange e) <= snd (syntaxErrorRange e)) errs
    , testProperty "memoisation does not change recovered trees and errors" $
        forAll (T.pack <$> listOf (elements "ab []\n\n")) $ \t ->
          let run cfg = let (tree, errs, _) = Recover.peg'parseSyntaxRecoverWith cfg t in (debugTree Recover.nameOfSyntaxKind tree, errs)
           in run defaultConfig {cfgMemo = False} === run defaultConfig
    , testCase "a valid input never reports errors in recovery mode" $
        mapM_ (\t -> snd (Recover.parseRecover t) @?= []) ["x", "x\n\ny", "[a]", "[a [b c] d]\n"]
    ]
