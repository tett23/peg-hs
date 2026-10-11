-- | JSON conformance (ADR 0010), run against nst/JSONTestSuite.
module Main (main) where

import qualified Conformance.Json.Encode as Encode
import Conformance.Json.Parser (Value (..))
import qualified Conformance.Json.Parser as Json
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.Either (isRight)
import Data.List (isPrefixOf, sort)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Codegen (Options (..), generateFromSource)
import Peg.Runtime (renderParseError)
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
      ]

regenerated :: Assertion
regenerated = do
  src <- TIO.readFile "json/Json.peg"
  committed <- B.readFile "json/Conformance/Json/Parser.hs"
  let opts = Options {optSourceName = "json/Json.peg", optOutputName = "json/Conformance/Json/Parser.hs", optDebugEntry = False}
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
