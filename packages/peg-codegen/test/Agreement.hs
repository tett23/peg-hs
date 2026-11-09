{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The interpreter agrees with the generated parsers (ADR 0090): on the
-- fixtures that it accepts, the errors, the syntax trees and the recovered
-- trees and errors are those of the committed generated modules.
module Agreement (agreementTests) where

import Control.Exception (finally)
import Data.List (nub, sort)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Differential (differentialEntries, differentialGrammar, differentialInputs)
import qualified Fixture.Arith as Arith
import qualified Fixture.Calc as Calc
import qualified Fixture.Differential as Differential
import qualified Fixture.Discard as Discard
import qualified Fixture.DiscardSyntax as DiscardSyntax
import qualified Fixture.Expect as Expect
import qualified Fixture.ExpectSyntax as ExpectSyntax
import qualified Fixture.Extensions as Extensions
import qualified Fixture.Generated as Generated
import qualified Fixture.GeneratedNames as GeneratedNames
import qualified Fixture.GeneratedPlain as GeneratedPlain
import qualified Fixture.Indent as Indent
import qualified Fixture.Located as Located
import qualified Fixture.Misc as Misc
import qualified Fixture.NoMemo as NoMemo
import qualified Fixture.Recover as Recover
import qualified Fixture.RecoverInsert as RecoverInsert
import qualified Fixture.RecoverLeft as RecoverLeft
import qualified Fixture.RecoverShared as RecoverShared
import qualified Fixture.RecoverVoid as RecoverVoid
import qualified Fixture.RecoverVoidSyntax as RecoverVoidSyntax
import qualified Fixture.Runs as Runs
import qualified Fixture.RunsSyntax as RunsSyntax
import qualified Fixture.Sum as Sum
import qualified Fixture.Syntax as Syntax
import qualified Fixture.Templates as Templates
import qualified Fixture.TemplatesSyntax as TemplatesSyntax
import qualified Fixture.Unicode as Unicode
import qualified Fixture.UnicodeSyntax as UnicodeSyntax
import qualified Fixture.UnitAnnotations as UnitAnnotations
import qualified Fixture.Units as Units
import qualified Fixture.UnitsSyntax as UnitsSyntax
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Interpret
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Peg.Runtime (ParseError, SyntaxError)
import Peg.Runtime.Syntax (SyntaxKind, SyntaxNode, debugTree)
import System.Directory (listDirectory)
import GHC.Conc (disableAllocationLimit, enableAllocationLimit, setAllocationCounter)
import System.FilePath (dropExtension, takeExtension)
import System.Timeout (timeout)
import Test.Tasty
import Test.Tasty.HUnit

-- What a generated module gives for one entry point: the errors of
-- @parse@, the tree of @parseSyntax@ and the recovered tree and errors of
-- @parseSyntaxRecover@ (with @%syntax@), the errors of @parseRecover@
-- (with labels), and the names of the kinds.
data Entry = Entry
  { entryRule :: Maybe Text
  , entryParse :: Text -> Either ParseError ()
  , entrySyntax :: Maybe (Text -> Either ParseError SyntaxNode)
  , entryRecover :: Maybe (Text -> (SyntaxNode, [SyntaxError]))
  , entryRecoverErrors :: Maybe (Text -> [SyntaxError])
  , entryKindName :: SyntaxKind -> Text
  }

plainEntry :: Maybe Text -> (Text -> Either ParseError a) -> Entry
plainEntry k p = Entry k (fmap (const ()) . p) Nothing Nothing Nothing (const "")

syntaxEntry :: Maybe Text -> (Text -> Either ParseError a) -> (Text -> Either ParseError SyntaxNode) -> (SyntaxKind -> Text) -> Entry
syntaxEntry k p s = Entry k (fmap (const ()) . p) (Just s) Nothing Nothing

withRecover :: (Text -> (SyntaxNode, [SyntaxError])) -> Entry -> Entry
withRecover r e = e {entryRecover = Just r}

withRecoverErrors :: (Text -> (a, [SyntaxError])) -> Entry -> Entry
withRecoverErrors r e = e {entryRecoverErrors = Just (snd . r)}

-- The fixtures that the interpreter accepts, with their entry points and
-- the inputs that their tests use. The list is checked against the
-- fixtures, so that a change of what the interpreter accepts is noticed.
targets :: [(String, [Entry], [Text])]
targets =
  [ ("Arith", [plainEntry Nothing Arith.parse, plainEntry (Just "Term") Arith.parseTerm], ["2*3+4", "10-3-2", "2^3^2", "2*(3+4)", "2*3", "2+3", "1+*2", "(1+2", "2^^3", "1+2*(3+4)-5^2", "((((1))))"])
  , ("Calc", [plainEntry Nothing Calc.parse, plainEntry (Just "H") Calc.parseH], ["x(n)(n).x(n).x", "1+2+3", "7", "x(n).x."])
  , ("Discard", [withRecoverErrors Discard.parseRecover (plainEntry Nothing Discard.parse)], [unusedInput])
  , ( "DiscardSyntax"
    , [withRecover DiscardSyntax.parseSyntaxRecover (syntaxEntry Nothing DiscardSyntax.parse DiscardSyntax.parseSyntax DiscardSyntax.nameOfSyntaxKind)]
    , [unusedInput]
    )
  , ("Expect", [withRecoverErrors Expect.parseRecover (plainEntry Nothing Expect.parse), withRecoverErrors Expect.parseRecoverOdd (plainEntry (Just "Odd") Expect.parseOdd)], expectInputs)
  , ( "ExpectSyntax"
    , [ withRecover ExpectSyntax.parseSyntaxRecover (syntaxEntry Nothing ExpectSyntax.parse ExpectSyntax.parseSyntax ExpectSyntax.nameOfSyntaxKind)
      , withRecover ExpectSyntax.parseSyntaxRecoverOdd (syntaxEntry (Just "Odd") ExpectSyntax.parseOdd ExpectSyntax.parseSyntaxOdd ExpectSyntax.nameOfSyntaxKind)
      ]
    , expectInputs
    )
  , ("Extensions", [plainEntry Nothing Extensions.parse, plainEntry (Just "Term") Extensions.parseTerm], ["2*3+4", "2+3", "1+*2"])
  , ("Generated", [plainEntry Nothing Generated.parse, plainEntry (Just "Atom") Generated.parseAtom, plainEntry (Just "Paren") Generated.parseParen], ["1+2", "(1)", "( 1 + 2 )"])
  , ("GeneratedNames", [plainEntry Nothing GeneratedNames.parse, plainEntry (Just "Count") GeneratedNames.parseCount, plainEntry (Just "Flags") GeneratedNames.parseFlags], ["a, b [y n 3] 1 #c,d", "a,b,c", "y 1"])
  , ("GeneratedPlain", [plainEntry Nothing GeneratedPlain.parse], ["a,b"])
  , ("Indent", [plainEntry Nothing Indent.parse], ["a\n  b\n\tc\n    d\ne\n", "a\n\tb\n", "a\n\tb\n\t!\n", "a\n  b\n  !\n", "a\n b\n", "a\n  b\nc\n"])
  , ("Located", [plainEntry Nothing Located.parse], ["1+22"])
  , ("Misc", [plainEntry Nothing Misc.parse], ["  foo_1 42 \"a\\\"b\" <ab12,_> あう \x1F600\n", "foo !", "foo 1 <a1,_> bar"])
  , ("NoMemo", [plainEntry Nothing NoMemo.parse], ["foo 1 <a1,_> bar", "foo !"])
  , ( "Recover"
    , [withRecoverErrors Recover.parseRecover (withRecover Recover.parseSyntaxRecover (syntaxEntry Nothing Recover.parse Recover.parseSyntax Recover.nameOfSyntaxKind))]
    , ["ok\n\n] broken", "x [ y]", "a [b c] d\n\ne [f]", "good one\n\n] broken [x\n\ngood two", "see [b unclosed\n\nnext", "x", "x\n\ny", "[a]", "[a [b c] d]\n", "ab[] \n"]
    )
  , ( "RecoverInsert"
    , [withRecoverErrors RecoverInsert.parseRecover (withRecover RecoverInsert.parseSyntaxRecover (syntaxEntry Nothing RecoverInsert.parse RecoverInsert.parseSyntax RecoverInsert.nameOfSyntaxKind))]
    , []
    )
  , ( "RecoverLeft"
    , [ withRecover RecoverLeft.parseSyntaxRecover (syntaxEntry Nothing RecoverLeft.parse RecoverLeft.parseSyntax RecoverLeft.nameOfSyntaxKind)
      , withRecover RecoverLeft.parseSyntaxRecoverD (syntaxEntry (Just "D") RecoverLeft.parseD RecoverLeft.parseSyntaxD RecoverLeft.nameOfSyntaxKind)
      ]
    , ["(aa)", "(ab)", "(a)", "()", "(a)(", "(aab)"]
    )
  , ("RecoverShared", [withRecoverErrors RecoverShared.parseRecover (plainEntry Nothing RecoverShared.parse)], [])
    -- The labels with a recovery rule where the values are not used (ADR 0094).
  , ("RecoverVoid", [withRecoverErrors RecoverVoid.parseRecover (plainEntry Nothing RecoverVoid.parse)], ["rx;", "ry;", "r;", "&xx;", "&yx;", "&zx;", "ry;&xx;rx;", "&z;rx;"])
  , ( "RecoverVoidSyntax"
    , [withRecover RecoverVoidSyntax.parseSyntaxRecover (syntaxEntry Nothing RecoverVoidSyntax.parse RecoverVoidSyntax.parseSyntax RecoverVoidSyntax.nameOfSyntaxKind)]
    , ["?x;", "?;", "?y;", "*xx;", "*;", "*y;", "+x;", "+xx;", "+y;", "+;", "!x;", "!y;", "!;", "+y;!y;?x;", "!yy;*x;"]
    )
  , ("Runs", [plainEntry Nothing Runs.parse, plainEntry (Just "PlainDoc") Runs.parsePlainDoc, plainEntry (Just "DeepDoc") Runs.parseDeepDoc], [runsInput])
  , ( "RunsSyntax"
    , [ syntaxEntry Nothing RunsSyntax.parse RunsSyntax.parseSyntax RunsSyntax.nameOfSyntaxKind
      , syntaxEntry (Just "PlainDoc") RunsSyntax.parsePlainDoc RunsSyntax.parseSyntaxPlainDoc RunsSyntax.nameOfSyntaxKind
      , syntaxEntry (Just "DeepDoc") RunsSyntax.parseDeepDoc RunsSyntax.parseSyntaxDeepDoc RunsSyntax.nameOfSyntaxKind
      ]
    , [runsInput]
    )
  , ("Sum", [plainEntry Nothing Sum.parse], ["1+2+3", "1+"])
  , ( "Syntax"
    , [syntaxEntry Nothing Syntax.parse Syntax.parseSyntax Syntax.nameOfSyntaxKind, syntaxEntry (Just "Term") Syntax.parseTerm Syntax.parseSyntaxTerm Syntax.nameOfSyntaxKind]
    , ["2 * 3", "1", "1 + 2", "1+2*3", "1 + 2 * (3 # three\n - 4)", "  1", "(1", "1 + # trailing", "2 * 3 - 4 * 5 + 6"]
    )
  , ("Templates", [plainEntry Nothing Templates.parse], [templateInput])
  , ("TemplatesSyntax", [syntaxEntry Nothing TemplatesSyntax.parse TemplatesSyntax.parseSyntax TemplatesSyntax.nameOfSyntaxKind], [templateInput])
  , ("Unicode", [plainEntry Nothing Unicode.parse], ["1＋20＋300"])
  , ("UnicodeSyntax", [syntaxEntry Nothing UnicodeSyntax.parse UnicodeSyntax.parseSyntax UnicodeSyntax.nameOfSyntaxKind], ["1＋20＋300", "1＋20"])
  , ("UnitAnnotations", [plainEntry Nothing UnitAnnotations.parse], [])
  , ("Units", [plainEntry Nothing Units.parse], ["1, 2,3;4; 5;  "])
  , ("UnitsSyntax", [syntaxEntry Nothing UnitsSyntax.parse UnitsSyntax.parseSyntax UnitsSyntax.nameOfSyntaxKind], ["1, 2,3;4; 5;  ", "1;2;; "])
  ]
  where
    unusedInput = "$12;$ab;&x1;!.;*1a2;?z;?;^42;"
    expectInputs = ["(1+2", "(1+2)", "x", "o", "1+", "", "1+(2"]
    runsInput = "- a\n  - b\n    deep\n\n  - c\n- d\n\n= t\n  x\n\n  - e\ny\n"
    templateInput = "lists 1, 2; 3 expr 1 + 2 + 3 vars a, b"

-- The entry points of the fixture of random grammars.
differential :: [Entry]
differential = zipWith entry (Nothing : map Just (drop 1 differentialEntries)) differentialParsers
  where
    entry k (p, s, r) = withRecover r (syntaxEntry k p s Differential.nameOfSyntaxKind)

differentialParsers :: [(Text -> Either ParseError (), Text -> Either ParseError SyntaxNode, Text -> (SyntaxNode, [SyntaxError]))]
differentialParsers =
  [ (Differential.parse, Differential.parseSyntax, Differential.parseSyntaxRecover)
  , (Differential.parseD2_S, Differential.parseSyntaxD2_S, Differential.parseSyntaxRecoverD2_S)
  , (Differential.parseD3_S, Differential.parseSyntaxD3_S, Differential.parseSyntaxRecoverD3_S)
  , (Differential.parseD4_S, Differential.parseSyntaxD4_S, Differential.parseSyntaxRecoverD4_S)
  , (Differential.parseD5_S, Differential.parseSyntaxD5_S, Differential.parseSyntaxRecoverD5_S)
  , (Differential.parseD6_S, Differential.parseSyntaxD6_S, Differential.parseSyntaxRecoverD6_S)
  , (Differential.parseD7_S, Differential.parseSyntaxD7_S, Differential.parseSyntaxRecoverD7_S)
  , (Differential.parseD8_S, Differential.parseSyntaxD8_S, Differential.parseSyntaxRecoverD8_S)
  , (Differential.parseD9_S, Differential.parseSyntaxD9_S, Differential.parseSyntaxRecoverD9_S)
  , (Differential.parseD10_S, Differential.parseSyntaxD10_S, Differential.parseSyntaxRecoverD10_S)
  , (Differential.parseD11_S, Differential.parseSyntaxD11_S, Differential.parseSyntaxRecoverD11_S)
  , (Differential.parseD12_S, Differential.parseSyntaxD12_S, Differential.parseSyntaxRecoverD12_S)
  , (Differential.parseD13_S, Differential.parseSyntaxD13_S, Differential.parseSyntaxRecoverD13_S)
  , (Differential.parseD14_S, Differential.parseSyntaxD14_S, Differential.parseSyntaxRecoverD14_S)
  , (Differential.parseD15_S, Differential.parseSyntaxD15_S, Differential.parseSyntaxRecoverD15_S)
  , (Differential.parseD16_S, Differential.parseSyntaxD16_S, Differential.parseSyntaxRecoverD16_S)
  , (Differential.parseD17_S, Differential.parseSyntaxD17_S, Differential.parseSyntaxRecoverD17_S)
  , (Differential.parseD18_S, Differential.parseSyntaxD18_S, Differential.parseSyntaxRecoverD18_S)
  , (Differential.parseD19_S, Differential.parseSyntaxD19_S, Differential.parseSyntaxRecoverD19_S)
  , (Differential.parseD20_S, Differential.parseSyntaxD20_S, Differential.parseSyntaxRecoverD20_S)
  , (Differential.parseD21_S, Differential.parseSyntaxD21_S, Differential.parseSyntaxRecoverD21_S)
  , (Differential.parseD22_S, Differential.parseSyntaxD22_S, Differential.parseSyntaxRecoverD22_S)
  , (Differential.parseD23_S, Differential.parseSyntaxD23_S, Differential.parseSyntaxRecoverD23_S)
  , (Differential.parseD24_S, Differential.parseSyntaxD24_S, Differential.parseSyntaxRecoverD24_S)
  , (Differential.parseD25_S, Differential.parseSyntaxD25_S, Differential.parseSyntaxRecoverD25_S)
  , (Differential.parseD26_S, Differential.parseSyntaxD26_S, Differential.parseSyntaxRecoverD26_S)
  , (Differential.parseD27_S, Differential.parseSyntaxD27_S, Differential.parseSyntaxRecoverD27_S)
  , (Differential.parseD28_S, Differential.parseSyntaxD28_S, Differential.parseSyntaxRecoverD28_S)
  , (Differential.parseD29_S, Differential.parseSyntaxD29_S, Differential.parseSyntaxRecoverD29_S)
  , (Differential.parseD30_S, Differential.parseSyntaxD30_S, Differential.parseSyntaxRecoverD30_S)
  , (Differential.parseD31_S, Differential.parseSyntaxD31_S, Differential.parseSyntaxRecoverD31_S)
  , (Differential.parseD32_S, Differential.parseSyntaxD32_S, Differential.parseSyntaxRecoverD32_S)
  , (Differential.parseD33_S, Differential.parseSyntaxD33_S, Differential.parseSyntaxRecoverD33_S)
  , (Differential.parseD34_S, Differential.parseSyntaxD34_S, Differential.parseSyntaxRecoverD34_S)
  , (Differential.parseD35_S, Differential.parseSyntaxD35_S, Differential.parseSyntaxRecoverD35_S)
  , (Differential.parseD36_S, Differential.parseSyntaxD36_S, Differential.parseSyntaxRecoverD36_S)
  , (Differential.parseD37_S, Differential.parseSyntaxD37_S, Differential.parseSyntaxRecoverD37_S)
  , (Differential.parseD38_S, Differential.parseSyntaxD38_S, Differential.parseSyntaxRecoverD38_S)
  , (Differential.parseD39_S, Differential.parseSyntaxD39_S, Differential.parseSyntaxRecoverD39_S)
  , (Differential.parseD40_S, Differential.parseSyntaxD40_S, Differential.parseSyntaxRecoverD40_S)
  , (Differential.parseD41_S, Differential.parseSyntaxD41_S, Differential.parseSyntaxRecoverD41_S)
  , (Differential.parseD42_S, Differential.parseSyntaxD42_S, Differential.parseSyntaxRecoverD42_S)
  , (Differential.parseD43_S, Differential.parseSyntaxD43_S, Differential.parseSyntaxRecoverD43_S)
  , (Differential.parseD44_S, Differential.parseSyntaxD44_S, Differential.parseSyntaxRecoverD44_S)
  , (Differential.parseD45_S, Differential.parseSyntaxD45_S, Differential.parseSyntaxRecoverD45_S)
  , (Differential.parseD46_S, Differential.parseSyntaxD46_S, Differential.parseSyntaxRecoverD46_S)
  , (Differential.parseD47_S, Differential.parseSyntaxD47_S, Differential.parseSyntaxRecoverD47_S)
  , (Differential.parseD48_S, Differential.parseSyntaxD48_S, Differential.parseSyntaxRecoverD48_S)
  , (Differential.parseD49_S, Differential.parseSyntaxD49_S, Differential.parseSyntaxRecoverD49_S)
  , (Differential.parseD50_S, Differential.parseSyntaxD50_S, Differential.parseSyntaxRecoverD50_S)
  ]

agreementTests :: TestTree
agreementTests =
  testGroup
    "the interpreter agrees with the generated parsers (ADR 0090)"
    [ testCase "the fixtures that the interpreter accepts" $ do
        files <- sort . filter ((== ".hpeg") . takeExtension) <$> listDirectory "test/fixtures"
        accepted <- filter (either (const False) (const True) . snd) <$> mapM (\f -> (,) (dropExtension f) . prepare <$> TIO.readFile ("test/fixtures/" <> f)) files
        map fst accepted @?= sort [n | (n, _, _) <- targets]
    , testCase "the random grammars are those of the generator" $ do
        src <- TIO.readFile "test/random/Differential.txt"
        src @?= differentialGrammar
    , testGroup "fixtures" [fixtureTest name entries inputs | (name, entries, inputs) <- targets]
    , testGroup
        "random grammars (test/random/Differential.txt)"
        [ testCase (T.unpack name) $ do
            ip <- TIO.readFile "test/random/Differential.txt" >>= either (\ds -> assertFailure (show ds) >> error "unreachable") pure . prepare
            agree ip differentialInputs e
        | (name, e) <- zip differentialEntries differential
        ]
    ]

fixtureTest :: String -> [Entry] -> [Text] -> TestTree
fixtureTest name entries inputs = testCase name . (if name `elem` boundedFixtures then bounded else id) $ do
  src <- TIO.readFile ("test/fixtures/" <> name <> ".hpeg")
  ip <- either (\ds -> assertFailure (show ds) >> error "unreachable") pure (prepare src)
  let all' = nub (inputs ++ short (alphabet src))
  mapM_ (agree ip all') entries

-- The fixtures whose recovering parses did not end before ADR 0095. Their
-- tests fail after 10 seconds or 4 GB of allocation instead of hanging.
boundedFixtures :: [String]
boundedFixtures = ["RecoverLeft"]

bounded :: Assertion -> Assertion
bounded a = do
  r <- timeout 10_000_000 $ do
    setAllocationCounter 4_000_000_000
    enableAllocationLimit
    a `finally` disableAllocationLimit
  maybe (assertFailure "the parses did not end in 10 seconds") pure r

-- Compare the interpreter with an entry point on the inputs.
agree :: Interpreter -> [Text] -> Entry -> Assertion
agree ip inputs e = do
  let k = entryRule e
      bad =
        [ (t, what)
        | t <- inputs
        , what <-
            [ "parse" | fmap (const ()) (interpret ip k t) /= entryParse e t
            ]
              ++ [ "parseSyntax"
                 | Just s <- [entrySyntax e]
                 , fmap (debugTree (interpreterKindName ip)) (interpret ip k t) /= fmap (debugTree (entryKindName e)) (s t)
                 ]
              ++ [ "parseSyntaxRecover"
                 | Just r <- [entryRecover e]
                 , let (tree, errs) = interpretRecover ip k t
                       (tree', errs') = r t
                 , (debugTree (interpreterKindName ip) tree, errs) /= (debugTree (entryKindName e) tree', errs')
                 ]
              ++ [ "parseRecover"
                 | Just r <- [entryRecoverErrors e]
                 , snd (interpretRecover ip k t) /= r t
                 ]
        ]
  case bad of
    [] -> pure ()
    (t, what) : _ ->
      assertFailure
        ( show (length bad) <> " disagreements of " <> show k <> ", the first: " <> what <> " of " <> show t
            <> "\ninterpreter: " <> show (interpret ip k t)
            <> "\nrecovering: " <> show (snd (interpretRecover ip k t))
        )

-- Every string of length 3 or less of the characters at the ends of the
-- literals and the classes of the grammar.
short :: [Char] -> [Text]
short cs = map T.pack (concatMap (\n -> sequence (replicate n cs)) [0 .. 3 :: Int])

alphabet :: Text -> [Char]
alphabet src = case parseGrammar src >>= expandTemplates of
  Left _ -> []
  Right g -> nub (concat [c | r <- grammarRules g, a <- ruleAlts r, i <- altItems a, c <- chars (itemExpr i)])
  where
    chars e = case e of
      ELit t _ -> [ends (T.unpack t)]
      EClass rs _ -> [concat [[a, b] | (a, b) <- rs]]
      EGroup alts -> concatMap (concatMap (chars . itemExpr)) alts
      EStar x -> chars x
      EPlus x -> chars x
      EOpt x -> chars x
      EAnd x -> chars x
      ENot x -> chars x
      ECapture x -> chars x
      ELabel _ x _ -> chars x
      EDiscard x -> chars x
      _ -> []
    ends s = nub (take 1 s ++ take 1 (reverse s))

prepare :: Text -> Either [Diagnostic] Interpreter
prepare src = do
  g0 <- parseGrammar src
  g <- either (Left . templateNotes g0) Right (expandTemplates g0)
  an <- either (Left . templateNotes g0) Right (check g)
  either (Left . templateNotes g0) Right (interpreter g an)
