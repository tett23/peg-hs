{-# LANGUAGE LambdaCase #-}

-- | JSON conformance (ADR 0010), run against nst/JSONTestSuite.
module Main (main) where

import qualified Conformance.Bench.JsonGenerated as JsonGenerated
import qualified Conformance.Bench.JsonLabeled as JsonLabeled
import qualified Conformance.Bench.JsonNomemo as JsonNomemo
import qualified Conformance.Bench.JsonRecover as JsonRecover
import qualified Conformance.Bench.JsonSyntax as JsonSyntax
import qualified Conformance.Bench.JsonUntyped as JsonUntyped
import Peg.Runtime.Syntax (debugTree, syntaxText)
import qualified Conformance.Json.Encode as Encode
import Conformance.Json.Parser (Value (..))
import qualified Conformance.Json.Parser as Json
import Data.Char (chr, digitToInt, ord)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.Either (isRight)
import Data.List (isPrefixOf, sort)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Codegen (Options (..), generateFromSource)
import Peg.Grammar.LabelInsertion (Insertion (..), insertLabels)
import Peg.Runtime (ParseError (..), SyntaxError (..), renderParseError)
import System.Directory (listDirectory)
import System.FilePath ((</>))
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

dataDir :: FilePath
dataDir = "data/JSONTestSuite/test_parsing"

-- Decode strictly as UTF-8, then parse. A decoding failure is a rejection.
parseFile :: FilePath -> IO (Either Text Value)
parseFile name = do
  bytes <- B.readFile (dataDir </> name)
  pure $ case TE.decodeUtf8' bytes of
    Left _ -> Left (T.pack "invalid UTF-8")
    Right t -> either (Left . renderParseError) Right (Json.parse t)

main :: IO ()
main = do
  files <- sort <$> listDirectory dataDir
  let named p = filter (p `isPrefixOf`) files
  defaultMain $
    testGroup
      "JSON (ADR 0010)"
      [ testCase "the committed parser is up to date" regenerated
      , testGroup "y_: accept" [testCase f (parseFile f >>= \r -> assertBool (show r) (isRight r)) | f <- named "y_"]
      , testGroup "n_: reject" [testCase f (parseFile f >>= \r -> assertBool (show r) (not (isRight r))) | f <- named "n_"]
      , goldenVsString "i_: recorded results" "json/implementation-defined.golden" (implementationDefined (named "i_"))
      , goldenVsString "error positions" "json/errors.golden" errorReport
      , testProperty "round trip" roundTrip
      , testGroup
          "lossless syntax tree (ADR 0019)"
          [ testCase "the text of the tree is the input, for every accepted case" $ do
              rs <- mapM (\f -> (,) f <$> losslessOnFile f) (named "y_" ++ named "i_")
              assertBool ("not lossless: " <> show [f | (f, False) <- rs]) (all snd rs)
          , testCase "the syntax variant accepts and rejects the same files" $ do
              rs <- mapM (\f -> (,) f <$> syntaxAgrees f) files
              assertBool ("different results: " <> show [f | (f, False) <- rs]) (all snd rs)
          , testProperty "lossless on generated documents" $
              forAll (sized genValue) $ \v ->
                let t = Encode.encode v in fmap syntaxText (JsonSyntax.parseSyntax t) === Right t
          ]
      , testGroup
          "the grammar without type annotations, actions and bindings (ADR 0068)"
          [ testProperty "the same tree as the typed %syntax grammar on generated documents" $
              forAll (sized genValue) $ \v ->
                let t = Encode.encode v in untypedTree t === typedTree t
          , testCase "the same tree as the typed %syntax grammar, or the same rejection, on every file" $ do
              rs <- mapM (\f -> (,) f <$> untypedAgrees f) files
              assertBool ("different trees: " <> show [f | (f, False) <- rs]) (all snd rs)
          ]
      , testGroup
          "the grammar whose types are inferred and generated (ADR 0075)"
          [ testProperty "the same values as the typed grammar on generated documents" $
              forAll (sized genValue) $ \v ->
                let t = Encode.encode v in generatedResult t === typedResult t
          , testCase "the same values and errors as the typed grammar on every file" $ do
              rs <- mapM (\f -> (,) f <$> generatedAgrees f) files
              assertBool ("different results: " <> show [f | (f, False) <- rs]) (all snd rs)
          ]
      , testGroup
          "recovery (ADR 0021)"
          [ testCase "the labelled grammar is the base grammar plus labels and recovery rules" labelledDerived
          , testCase "labels do not change the accepted language" $ do
              rs <- mapM (\f -> (,) f <$> labelsAgree f) files
              assertBool ("different results: " <> show [f | (f, False) <- rs]) (all snd rs)
          , testCase "labels do not change the accepted language on mutated valid cases (ADR 0028)" $ do
              srcs <- mapM (\f -> TE.decodeUtf8' <$> B.readFile (dataDir </> f)) (named "y_")
              let mutants t = concat [[T.take i t <> T.drop (i + 1) t, T.take (i + 1) t <> T.drop i t] | i <- [0 .. T.length t - 1]]
                  bad = [m | Right t <- srcs, m <- mutants t, isRight (Json.parse m) /= isRight (JsonRecover.parse m)]
              assertBool ("differ: " <> show (take 3 bad)) (null bad)
          , testCase "every rejected case gives a lossless tree with errors" $ do
              rs <- mapM (\f -> (,) f <$> recoversOnFile f) (named "n_")
              assertBool ("failed: " <> show [f | (f, False) <- rs]) (all snd rs)
          , testProperty "every input gives a lossless tree" $
              forAll (T.pack <$> arbitrary) $ \t ->
                syntaxText (fst (JsonRecover.parseSyntaxRecover t)) === t
          , testProperty "every near-JSON input gives a lossless tree" $
              forAll (T.pack <$> listOf (elements "[]{},:\"\\0123456789.eE+-truefalsn \n\x3042")) $ \t ->
                syntaxText (fst (JsonRecover.parseSyntaxRecover t)) === t
          , testCase "a broken element is recovered in place" $ do
              let (v, errs) = JsonRecover.parseRecover (T.pack "[1, @, 3]")
              fmap show v @?= Just (show (JsonRecover.Array [JsonRecover.Number (T.pack "1"), JsonRecover.Null, JsonRecover.Number (T.pack "3")]))
              map syntaxErrorLabel errs @?= [Just (T.pack "value")]
          ]
      , testGroup
          "labels inserted by peg-hs label (ADR 0054)"
          [ testCase "the grammar is json/Json.hpeg with the labels of peg-hs label, and its parser is up to date" labeledDerived
          , testCase "the labels do not change the accepted language" $ do
              rs <- mapM (\f -> (,) f <$> labeledAgree f) files
              assertBool ("different results: " <> show [f | (f, False) <- rs]) (all snd rs)
          , testCase "the labels do not change the accepted language on mutated valid cases" $ do
              srcs <- mapM (\f -> TE.decodeUtf8' <$> B.readFile (dataDir </> f)) (named "y_")
              let mutants t = concat [[T.take i t <> T.drop (i + 1) t, T.take (i + 1) t <> T.drop i t] | i <- [0 .. T.length t - 1]]
                  bad = [m | Right t <- srcs, m <- mutants t, isRight (Json.parse m) /= isRight (JsonLabeled.parse m)]
              assertBool ("differ: " <> show (take 3 bad)) (null bad)
          , testCaseInfo "the rejected cases whose error names an inserted label" $ do
              src <- TIO.readFile "json/Json.hpeg"
              let inserted = either (const []) (map insertionName . fst) (insertLabels [] src)
              rs <- mapM (\f -> TE.decodeUtf8' <$> B.readFile (dataDir </> f)) files
              let rejected = [e | Right t <- rs, Left e <- [JsonLabeled.parse t]]
                  named' = [l | e <- rejected, Just l <- [parseErrorLabel e], l `elem` inserted]
              pure (show (length named') <> " of " <> show (length rejected) <> " rejected inputs, with " <> show (length inserted) <> " labels")
          ]
      , testGroup
          "%nomemo variant (ADR 0017)"
          [ testCase "the variant grammars are derived from json/Json.hpeg" variantsDerived
          , testCase "same results on the whole test suite" $ do
              rs <- mapM (\f -> (,) f <$> sameOnFile f) files
              assertBool ("different results: " <> show [f | (f, False) <- rs]) (all snd rs)
          , testProperty "same results and errors on arbitrary input" $
              forAll (T.pack <$> listOf (elements "[]{},:\"\\0123456789.eE+-truefalsn \n")) $ \t ->
                show (Json.parse t) === show (JsonNomemo.parse t)
          ]
      ]

regenerated :: Assertion
regenerated = do
  src <- TIO.readFile "json/Json.hpeg"
  committed <- B.readFile "json/Conformance/Json/Parser.hs"
  let opts = Options {optSourceName = "json/Json.hpeg", optOutputName = "json/Conformance/Json/Parser.hs", optDebugEntry = False, optExports = Nothing}
  case generateFromSource opts src of
    Left ds -> assertFailure (show ds)
    Right code -> assertBool "regenerate with scripts/regen-fixtures.sh" (TE.encodeUtf8 code == committed)

-- Accept or reject for each implementation-defined case. Which one is right
-- is not decided; the test catches unintended changes.
implementationDefined :: [FilePath] -> IO BL.ByteString
implementationDefined names = do
  results <- mapM (\f -> (,) f <$> parseFile f) names
  pure . BL.fromStrict . TE.encodeUtf8 . T.unlines $
    [T.pack f <> T.pack (if isRight r then " accept" else " reject") | (f, r) <- results]

-- Rendered errors of a few rejected inputs, reviewed by hand.
errorReport :: IO BL.ByteString
errorReport = do
  let cases =
        [ "n_array_extra_comma.json"
        , "n_object_missing_value.json"
        , "n_number_-01.json"
        , "n_string_unescaped_tab.json"
        , "n_structure_unclosed_array.json"
        , "n_object_trailing_comma.json"
        , "n_structure_100000_opening_arrays.json"
        ]
  results <- mapM (\f -> (,) f <$> parseFile f) cases
  pure . BL.fromStrict . TE.encodeUtf8 . T.unlines $
    [T.pack f <> T.pack ": " <> either id (const (T.pack "accepted")) r | (f, r) <- results]

-- Round trip ---------------------------------------------------------------------

genValue :: Int -> Gen Value
genValue n
  | n <= 0 = scalar
  | otherwise =
      frequency
        [ (3, scalar)
        , (1, Array <$> listOfSize (genValue (n `div` 3)))
        , (1, Object <$> listOfSize ((,) <$> genText <*> genValue (n `div` 3)))
        ]
  where
    listOfSize g = choose (0, 4) >>= \k -> vectorOf k g
    scalar =
      oneof
        [ pure Null
        , Bool <$> arbitrary
        , Number <$> genNumber
        , String <$> genText
        ]

genText :: Gen Text
genText = T.pack <$> listOf (frequency [(4, choose ('a', 'z')), (1, elements "\"\\/\n\t\x01 あ\x1F600"), (1, arbitrary)])

genNumber :: Gen Text
genNumber = do
  sign <- elements ["", "-"]
  int <- oneof [pure "0", (:) <$> choose ('1', '9') <*> listOf (choose ('0', '9'))]
  frac <- oneof [pure "", ('.' :) <$> listOf1 (choose ('0', '9'))]
  ex <- oneof [pure "", (\e s ds -> e : s <> ds) <$> elements "eE" <*> elements ["", "+", "-"] <*> listOf1 (choose ('0', '9'))]
  pure (T.pack (sign <> int <> frac <> ex))

roundTrip :: Property
roundTrip = forAll (sized genValue) $ \v -> Json.parse (Encode.encode v) === Right v

-- The variants of ADR 0017 must stay in sync with the base grammar. They
-- are written by scripts/regen-fixtures.sh.
variantsDerived :: Assertion
variantsDerived = do
  base <- TIO.readFile "json/Json.hpeg"
  let header = T.pack "%module Conformance.Json.Parser"
      derive m extra = T.replace header (T.pack ("%module " <> m) <> extra) base
      nomemo = T.concat [T.pack ("\n%nomemo " <> r) | r <- ["Ws", "Unit", "Hex", "IntPart", "Frac", "Exp"]]
      syntaxDirectives = T.pack "\n%syntax\n%token Ws\n%trivia Ws"
  counted <- TIO.readFile "bench/JsonCounted.hpeg"
  nm <- TIO.readFile "bench/JsonNomemo.hpeg"
  counted @?= derive "Conformance.Bench.JsonCounted" T.empty
  nm @?= derive "Conformance.Bench.JsonNomemo" nomemo
  sy <- TIO.readFile "bench/JsonSyntax.hpeg"
  sy @?= derive "Conformance.Bench.JsonSyntax" syntaxDirectives
  mapM_
    ( \(src, out) -> do
        grammar <- TIO.readFile src
        committed <- B.readFile out
        case generateFromSource (Options src out True Nothing) grammar of
          Left ds -> assertFailure (show ds)
          Right code -> assertBool ("regenerate " <> out) (TE.encodeUtf8 code == committed)
    )
    [ ("bench/JsonCounted.hpeg", "bench/Conformance/Bench/JsonCounted.hs")
    , ("bench/JsonNomemo.hpeg", "bench/Conformance/Bench/JsonNomemo.hs")
    , ("bench/JsonSyntax.hpeg", "bench/Conformance/Bench/JsonSyntax.hs")
    , ("bench/JsonUntyped.hpeg", "bench/Conformance/Bench/JsonUntyped.hs")
    , ("bench/JsonGenerated.hpeg", "bench/Conformance/Bench/JsonGenerated.hs")
    ]

-- Accept or reject the same way, with the same error.
sameOnFile :: FilePath -> IO Bool
sameOnFile name = do
  bytes <- B.readFile (dataDir </> name)
  pure $ case TE.decodeUtf8' bytes of
    Left _ -> True
    Right t -> show (Json.parse t) == show (JsonNomemo.parse t)

-- The syntax tree reproduces the input (ADR 0019).
losslessOnFile :: FilePath -> IO Bool
losslessOnFile name = do
  bytes <- B.readFile (dataDir </> name)
  pure $ case TE.decodeUtf8' bytes of
    Left _ -> True
    Right t -> case JsonSyntax.parseSyntax t of
      Right tree -> syntaxText tree == t
      Left _ -> True

syntaxAgrees :: FilePath -> IO Bool
syntaxAgrees name = do
  bytes <- B.readFile (dataDir </> name)
  pure $ case TE.decodeUtf8' bytes of
    Left _ -> True
    Right t -> either (Left . show) (const (Right ())) (Json.parse t) == either (Left . show) (const (Right ())) (JsonSyntax.parseSyntax t)

-- The trees of the grammar without type annotations, actions and bindings
-- (ADR 0068), and of the typed %syntax grammar, as debugTree writes them,
-- without the labels: the bindings of the typed grammar label children,
-- and the untyped grammar has no bindings.
untypedTree, typedTree :: Text -> Either String Text
untypedTree = either (Left . show) (Right . withoutLabels . debugTree JsonUntyped.nameOfSyntaxKind) . JsonUntyped.parseSyntax
typedTree = either (Left . show) (Right . withoutLabels . debugTree JsonSyntax.nameOfSyntaxKind) . JsonSyntax.parseSyntax

-- Remove the labels that debugTree writes before the kinds, as in
-- "  n: Number@1..2". Kinds start with an upper-case letter, labels here
-- with a lower-case one.
withoutLabels :: Text -> Text
withoutLabels = T.unlines . map line . T.lines
  where
    line l =
      let (indent, rest) = T.span (== ' ') l
          (name, kind) = T.breakOn (T.pack ": ") rest
       in case T.uncons name of
            Just (c, _) | c >= 'a' && c <= 'z' && T.all isIdent name && not (T.null kind) -> indent <> T.drop 2 kind
            _ -> l
    isIdent c = c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' || c == '_'

untypedAgrees :: FilePath -> IO Bool
untypedAgrees name = do
  bytes <- B.readFile (dataDir </> name)
  pure $ case TE.decodeUtf8' bytes of
    Left _ -> True
    Right t -> untypedTree t == typedTree t

-- The value of the grammar whose types are inferred and generated (ADR
-- 0075), mapped to the value of the typed grammar, and the value of the
-- typed grammar, with the errors as shown.
generatedResult, typedResult :: Text -> Either String Value
generatedResult = either (Left . show) (Right . fromGenerated) . JsonGenerated.parse
typedResult = either (Left . show) Right . Json.parse

generatedAgrees :: FilePath -> IO Bool
generatedAgrees name = do
  bytes <- B.readFile (dataDir </> name)
  pure $ case TE.decodeUtf8' bytes of
    Left _ -> True
    Right t -> generatedResult t == typedResult t

-- The generated types of JsonGenerated as the type of json/Json.hpeg. The
-- strings are decoded as the actions of json/Json.hpeg decode them.
fromGenerated :: JsonGenerated.Value -> Value
fromGenerated = \case
  JsonGenerated.Value1 -> Null
  JsonGenerated.Value2 -> Bool True
  JsonGenerated.Value3 -> Bool False
  JsonGenerated.Value4 n -> Number n
  JsonGenerated.Value5 us -> String (string us)
  JsonGenerated.Value6 (JsonGenerated.Array1 (JsonGenerated.Elements e es)) -> Array (map fromGenerated (e : es))
  JsonGenerated.Value6 JsonGenerated.Array2 -> Array []
  JsonGenerated.Value7 (JsonGenerated.Object1 (JsonGenerated.Members m ms)) -> Object [(string k, fromGenerated v) | JsonGenerated.Member k v <- m : ms]
  JsonGenerated.Value7 JsonGenerated.Object2 -> Object []
  where
    string = T.pack . decodeUnits . map unit
    unit = \case
      JsonGenerated.Unit1 e -> escape e
      JsonGenerated.Unit2 c -> ord (T.foldr const ' ' c)
    escape = \case
      JsonGenerated.Escape1 -> 0x22
      JsonGenerated.Escape2 -> 0x5C
      JsonGenerated.Escape3 -> 0x2F
      JsonGenerated.Escape4 -> 0x08
      JsonGenerated.Escape5 -> 0x0C
      JsonGenerated.Escape6 -> 0x0A
      JsonGenerated.Escape7 -> 0x0D
      JsonGenerated.Escape8 -> 0x09
      JsonGenerated.Escape9 h -> T.foldl' (\n c -> n * 16 + digitToInt c) 0 h
    -- As in json/Json.hpeg: UTF-16 surrogate pairs are joined, and a lone
    -- surrogate becomes U+FFFD.
    decodeUnits (hi : lo : rest)
      | 0xD800 <= hi && hi <= 0xDBFF && 0xDC00 <= lo && lo <= 0xDFFF =
          chr (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) : decodeUnits rest
    decodeUnits (u : rest)
      | 0xD800 <= u && u <= 0xDFFF = '\xFFFD' : decodeUnits rest
      | otherwise = chr u : decodeUnits rest
    decodeUnits [] = []

-- The labelled grammar differs from the base grammar only by its header,
-- its labels and its recovery rules.
labelledDerived :: Assertion
labelledDerived = do
  base <- TIO.readFile "json/Json.hpeg"
  labelled <- TIO.readFile "bench/JsonRecover.hpeg"
  let body = T.unlines . filter (\l -> not (any (`T.isPrefixOf` l) (map T.pack ["%syntax", "%token", "%trivia", "%recover"]))) . T.lines
      withoutRecovery = fst (T.breakOn (T.pack "\n# 回復の規則") labelled)
      unlabel = T.unwords . filter (not . T.isPrefixOf (T.pack "^")) . T.words
      normalise = map unlabel . T.lines . body
  normalise (T.replace (T.pack "Conformance.Bench.JsonRecover") (T.pack "Conformance.Json.Parser") withoutRecovery)
    @?= normalise (T.stripEnd base <> T.pack "\n")

-- The grammar with the labels of peg-hs label is written by
-- scripts/regen-fixtures.sh (ADR 0054).
labeledDerived :: Assertion
labeledDerived = do
  base <- TIO.readFile "json/Json.hpeg"
  committed <- TIO.readFile "bench/JsonLabeled.hpeg"
  let renamed = T.replace (T.pack "%module Conformance.Json.Parser") (T.pack "%module Conformance.Bench.JsonLabeled") base
  fmap snd (insertLabels [] renamed) @?= Right committed
  assertBool "labels are inserted" (committed /= renamed)
  code <- B.readFile "bench/Conformance/Bench/JsonLabeled.hs"
  case generateFromSource (Options "bench/JsonLabeled.hpeg" "bench/Conformance/Bench/JsonLabeled.hs" False Nothing) committed of
    Left ds -> assertFailure (show ds)
    Right out -> assertBool "regenerate bench/Conformance/Bench/JsonLabeled.hs" (TE.encodeUtf8 out == code)

labeledAgree :: FilePath -> IO Bool
labeledAgree name = do
  bytes <- B.readFile (dataDir </> name)
  pure $ case TE.decodeUtf8' bytes of
    Left _ -> True
    Right t -> isRight (Json.parse t) == isRight (JsonLabeled.parse t)

labelsAgree :: FilePath -> IO Bool
labelsAgree name = do
  bytes <- B.readFile (dataDir </> name)
  pure $ case TE.decodeUtf8' bytes of
    Left _ -> True
    Right t -> isRight (Json.parse t) == isRight (JsonRecover.parse t)

recoversOnFile :: FilePath -> IO Bool
recoversOnFile name = do
  bytes <- B.readFile (dataDir </> name)
  pure $ case TE.decodeUtf8' bytes of
    Left _ -> True
    Right t ->
      let (tree, errs) = JsonRecover.parseSyntaxRecover t
       in syntaxText tree == t && not (null errs)
