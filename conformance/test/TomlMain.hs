{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | TOML 1.1.0 conformance (ADR 0023), run against toml-test v2.2.0.
module Main (main) where

import qualified Conformance.Json.Parser as Json
import Conformance.Toml.Document (BuildError (..), Value (..), build)
import qualified Conformance.Toml.NoLabels as NoLabels
import qualified Conformance.Toml.Parser as Toml
import Conformance.Toml.Types (DateTime (..), Time (..))
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.List (sort)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Codegen (Options (..), generate, generateFromSource)
import Peg.Grammar.Labels (stripLabelsAs)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Runtime (ParseError (..), Pos (..), Span (..), SyntaxError (..), renderParseError)
import Peg.Runtime.Syntax
import System.FilePath (takeExtension, (</>))
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck (counterexample, elements, forAll, testProperty, withNumTests)

dataDir :: FilePath
dataDir = "data/toml-test"

-- The stage that rejected an input, or the document.
data Outcome
  = DecodeError
  | GrammarError ParseError
  | BuildFailure BuildError
  | Document (M.Map Text Value)

stageName :: Outcome -> Text
stageName = \case
  DecodeError -> "decode"
  GrammarError _ -> "grammar"
  BuildFailure _ -> "build"
  Document _ -> "accepted"

readInput :: FilePath -> IO (Either () Text)
readInput name = either (const (Left ())) Right . TE.decodeUtf8' <$> B.readFile (dataDir </> name)

outcome :: Either () Text -> Outcome
outcome = \case
  Left () -> DecodeError
  Right t -> case Toml.parse t of
    Left e -> GrammarError e
    Right ls -> either BuildFailure Document (build ls)

main :: IO ()
main = do
  listed <- filter ((== ".toml") . takeExtension) . map T.unpack . T.lines <$> TIO.readFile (dataDir </> "files-toml-1.1.0")
  let valid = sort [f | f <- listed, "valid/" `T.isPrefixOf` T.pack f]
      invalid = sort [f | f <- listed, "invalid/" `T.isPrefixOf` T.pack f]
  inputs <- M.fromList <$> mapM (\f -> (,) f <$> readInput f) listed
  let decoded = [(f, t) | (f, Right t) <- M.toList inputs]
      candidates = concatMap (uncurry breakable) [(f, t) | (f, t) <- decoded, f `elem` valid]
  defaultMain $
    testGroup
      "TOML 1.1.0 (ADR 0023)"
      [ testCase "the committed parser is up to date" regenerated
      , testCase "the committed parser without labels is up to date (ADR 0028)" regeneratedNoLabels
      , testCase "the grammar accepts the same inputs without its labels (ADR 0028)" $ do
          let mutants t =
                t : concat [[T.take i t <> T.drop (i + 1) t, T.take (i + 1) t <> T.drop i t] | i <- [0 .. T.length t - 1]]
              accepts p t = either (const False) (const True) (p t)
              bad = [m | (_, t) <- decoded, m <- mutants t, accepts Toml.parse m /= accepts NoLabels.parse m]
          assertBool (show (length bad) <> " inputs differ, the first ones: " <> show (take 3 bad)) (null bad)
      , testGroup "valid: the document is the expected JSON" [testCase f (validCase f (inputs M.! f)) | f <- valid]
      , testGroup "invalid: rejected" [testCase f (invalidCase (inputs M.! f)) | f <- invalid]
      , goldenVsString "invalid: the stage that rejects each input" "toml/invalid-stages.golden" $
          pure . BL.fromStrict . TE.encodeUtf8 . T.unlines $ [T.pack f <> " " <> stageName (outcome (inputs M.! f)) | f <- invalid]
      , testGroup
          "building"
          [ testCase "the largest integer" $ stageOf "a = 9223372036854775807" @?= "accepted"
          , testCase "the smallest integer" $ stageOf "a = -9223372036854775808" @?= "accepted"
          , testCase "an integer above the range" $ stageOf "a = 9223372036854775808" @?= "build"
          , testCase "a hexadecimal integer above the range" $ stageOf "a = 0x8000000000000000" @?= "build"
          , testCase "February 29 in a leap year" $ stageOf "a = 2024-02-29" @?= "accepted"
          , testCase "February 29 in 1900" $ stageOf "a = 1900-02-29" @?= "build"
          , testCase "an error has the range of its line" $
              case outcome (Right "a = 1\nb = 2\na = 3\n") of
                BuildFailure (BuildError (Just sp) _) -> (posLine (spanStart sp), posLine (spanEnd sp)) @?= (3, 3)
                other -> assertFailure (T.unpack (stageName other))
          ]
      , testGroup
          "recovery (ADR 0021)"
          [ testCase "every input gives a lossless tree" $ do
              let bad = [f | (f, t) <- decoded, syntaxText (fst (Toml.parseSyntaxRecover t)) /= t]
              bad @?= []
          , testCase "every input rejected by the grammar gives syntax errors near the failure" $ do
              let bad = [f | (f, t) <- decoded, f `elem` invalid, Left e <- [Toml.parse t], not (reportedNear t e (snd (Toml.parseSyntaxRecover t)))]
              bad @?= []
          , testCase "every valid input gives no syntax error" $ do
              let bad = [f | (f, t) <- decoded, f `elem` valid, not (null (snd (Toml.parseSyntaxRecover t)))]
              bad @?= []
          , testProperty ("a broken line is recovered in place (" <> show (length candidates) <> " candidates)") $
              withNumTests 2000 $
                forAll (elements candidates) $ \b ->
                  let r = recoveredInPlace b in counterexample r (null r)
          ]
      ]

stageOf :: Text -> Text
stageOf = stageName . outcome . Right

-- Valid cases ------------------------------------------------------------------

validCase :: FilePath -> Either () Text -> Assertion
validCase name input = case outcome input of
  Document doc -> do
    expected <- TIO.readFile (dataDir </> (take (length name - 5) name <> ".json"))
    case Json.parse expected of
      Left e -> assertFailure ("expected JSON: " <> T.unpack (renderParseError e))
      Right j -> case matches (Table doc) j of
        Nothing -> pure ()
        Just why -> assertFailure why
  other -> assertFailure ("rejected at " <> T.unpack (stageName other) <> ": " <> describe other)

describe :: Outcome -> String
describe = \case
  GrammarError e -> T.unpack (renderParseError e)
  BuildFailure (BuildError _ msg) -> T.unpack msg
  _ -> ""

-- Compare with the tagged JSON of toml-test: integers and floats by value,
-- NaN equal to NaN, date-times by their parts.
matches :: Value -> Json.Value -> Maybe String
matches v j = case (v, j) of
  (Table m, Json.Object kvs)
    | Just (ty, val) <- leaf kvs -> Just ("a table where a " <> T.unpack ty <> " " <> T.unpack val <> " was expected")
    | sort (M.keys m) /= sort (map fst kvs) -> Just ("keys " <> show (M.keys m) <> " /= " <> show (map fst kvs))
    | otherwise -> firstJust [matches x y | (k, y) <- kvs, Just x <- [M.lookup k m]]
  (Array xs, Json.Array ys)
    | length xs /= length ys -> Just ("array lengths " <> show (length xs) <> " /= " <> show (length ys))
    | otherwise -> firstJust (zipWith matches xs ys)
  (_, Json.Object kvs) | Just (ty, val) <- leaf kvs -> scalar ty val
  _ -> Just ("shape: " <> show v <> " against " <> show j)
  where
    scalar ty val = case (ty, v) of
      ("string", String s) | s == val -> Nothing
      ("integer", Integer i) | read (T.unpack val) == i -> Nothing
      ("bool", Bool b) | val == (if b then "true" else "false") -> Nothing
      ("float", Float d) | sameFloat d val -> Nothing
      (_, DateTimeValue dt)
        | Right e <- Toml.parseDateTime val, kind dt == ty, normalise dt == normalise e -> Nothing
      _ -> Just (show v <> " /= " <> T.unpack ty <> " " <> show val)
    kind (DateTime d t o) = case (d, t, o) of
      (Just _, Just _, Just _) -> "datetime"
      (Just _, Just _, Nothing) -> "datetime-local"
      (Just _, Nothing, _) -> "date-local"
      _ -> "time-local"
    normalise (DateTime d t o) = (d, fmap (\(Time h m s f) -> (h, m, s, T.dropWhileEnd (== '0') f)) t, o)

leaf :: [(Text, Json.Value)] -> Maybe (Text, Text)
leaf kvs = case (lookup "type" kvs, lookup "value" kvs) of
  (Just (Json.String ty), Just (Json.String val)) | length kvs == 2 -> Just (ty, val)
  _ -> Nothing

sameFloat :: Double -> Text -> Bool
sameFloat d val
  | T.dropWhile (`elem` ("+-" :: String)) val == "nan" = isNaN d
  | val `elem` ["inf", "+inf"] = d == 1 / 0
  | val == "-inf" = d == -1 / 0
  | otherwise = d == read (T.unpack (T.dropWhile (== '+') val))

firstJust :: [Maybe a] -> Maybe a
firstJust = foldr (\x acc -> maybe acc Just x) Nothing

-- Invalid cases ----------------------------------------------------------------

invalidCase :: Either () Text -> Assertion
invalidCase input = case outcome input of
  Document _ -> assertFailure "accepted"
  _ -> pure ()

-- Recovery ----------------------------------------------------------------------

-- The first syntax error overlaps the line of the farthest failure of the
-- entry point that does not recover.
reportedNear :: Text -> ParseError -> [SyntaxError] -> Bool
reportedNear t e errs = case errs of
  [] -> False
  first : _ ->
    let (s, end) = syntaxErrorRange first
        off = posOffset (parseErrorPos e)
        lineStart = maybe 0 (+ 1) (lastNewlineBefore off)
        lineEnd = maybe (B.length bytes) (+ off) (B.elemIndex 10 (B.drop off bytes))
     in s <= lineEnd && end >= lineStart
  where
    bytes = TE.encodeUtf8 t
    lastNewlineBefore off = B.elemIndexEnd 10 (B.take off bytes)

-- A single-line expression of a valid file, broken in one way.
data Break = Break
  { breakFile :: FilePath
  , breakKind :: Text
  , breakText :: Text
  -- ^ The broken input.
  , breakRange :: (Int, Int)
  -- ^ The byte range of the broken expression in the broken input.
  , breakOthers :: [(Text, [Text])]
  -- ^ The other expressions of the original: their text and the kinds of
  -- their child nodes.
  }

instance Show Break where
  show b = show (breakFile b, breakKind b, breakText b)

expressions :: SyntaxNode -> [SyntaxNode]
expressions n
  | syntaxKind n == Toml.syntaxKindExpression = [n]
  | otherwise = concatMap expressions (syntaxChildren n)

shape :: SyntaxNode -> (Text, [Text])
shape n = (syntaxText n, map (Toml.nameOfSyntaxKind . syntaxKind) (syntaxChildren n))

descendants :: SyntaxNode -> [SyntaxNode]
descendants n = n : concatMap descendants (syntaxChildren n)

-- Byte offsets: syntax ranges count bytes of the UTF-8 encoding.
cut :: Text -> Int -> Int -> Text
cut t from to = let b = TE.encodeUtf8 t in TE.decodeUtf8 (B.take from b <> B.drop to b)

breakable :: FilePath -> Text -> [Break]
breakable f t = case Toml.parseSyntax t of
  Left _ -> []
  Right tree ->
    let exprs = expressions tree
     in concat
          [ [ Break f kind (cut t a b) (s, e - (b - a)) [shape y | (j, y) <- zip [0 :: Int ..] exprs, j /= i]
            | (kind, (a, b)) <- cuts x
            ]
          | (i, x) <- zip [0 ..] exprs
          , let (s, e) = syntaxRange x
          , not (T.any (`elem` ("\r\n" :: String)) (syntaxText x))
          ]
  where
    cuts x =
      [("delete =", (p, p + 1)) | n <- descendants x, syntaxKind n == Toml.syntaxKindKeyValSep, Just k <- [T.findIndex (== '=') (syntaxText n)], let p = fst (syntaxRange n) + k]
        ++ [("delete the value", syntaxRange n) | n <- descendants x, syntaxKind n == Toml.syntaxKindVal, syntaxParent n `hasKind` Toml.syntaxKindKeyVal]
        ++ [("delete ]", (snd (syntaxRange n) - 1, snd (syntaxRange n))) | n <- descendants x, syntaxKind n `elem` [Toml.syntaxKindStdTableBody, Toml.syntaxKindArrayTableBody]]
    hasKind p k = fmap syntaxKind p == Just k

-- Every error node lies in the broken expression, and the other expressions
-- keep their text and kinds. Returns what went wrong, if anything.
recoveredInPlace :: Break -> String
recoveredInPlace b
  | syntaxText tree /= breakText b = "not lossless"
  | null errs = "no syntax error"
  | not (all inside errorNodes) = "error outside the line: " <> show (map syntaxRange errorNodes) <> " not in " <> show (breakRange b)
  | others /= breakOthers b = "other lines changed: " <> show (take 3 [(x, y) | (x, y) <- zip others (breakOthers b), x /= y])
  | otherwise = ""
  where
    (tree, errs) = Toml.parseSyntaxRecover (breakText b)
    errorNodes = [n | n <- descendants tree, syntaxKind n == errorKind]
    (s, e) = breakRange b
    inside n = let (x, y) = syntaxRange n in x >= s && y <= e
    others = [shape x | x <- expressions tree, fst (syntaxRange x) /= s]

regeneratedNoLabels :: Assertion
regeneratedNoLabels = do
  src <- TIO.readFile "toml/Toml.peg"
  committed <- B.readFile "toml/Conformance/Toml/NoLabels.hs"
  let opts = Options {optSourceName = "toml/Toml.peg", optOutputName = "toml/Conformance/Toml/NoLabels.hs", optDebugEntry = False}
  case parseGrammar src >>= generate opts . stripLabelsAs (T.pack "Conformance.Toml.NoLabels") of
    Left ds -> assertFailure (show ds)
    Right code -> assertBool "regenerate with scripts/regen-fixtures.sh" (TE.encodeUtf8 code == committed)

regenerated :: Assertion
regenerated = do
  src <- TIO.readFile "toml/Toml.peg"
  committed <- B.readFile "toml/Conformance/Toml/Parser.hs"
  let opts = Options {optSourceName = "toml/Toml.peg", optOutputName = "toml/Conformance/Toml/Parser.hs", optDebugEntry = False}
  case generateFromSource opts src of
    Left ds -> assertFailure (show ds)
    Right code -> assertBool "regenerate with scripts/regen-fixtures.sh" (TE.encodeUtf8 code == committed)
