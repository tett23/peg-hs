-- | Evaluation counts of left recursion stay within the quadratic bound of
-- ADR 0007, and the committed benchmark parser is up to date.
module Main (main) where

import qualified Conformance.Bench.NestedLR2 as NestedLR2
import qualified Conformance.Bench.NestedLR4 as NestedLR4
import qualified Conformance.Bench.NestedLR8 as NestedLR8
import qualified Conformance.Bench.Pathological as Pathological
import Peg.Runtime (ParseError)
import qualified Data.ByteString as B
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Codegen (Options (..), generateFromSource)
import Peg.Runtime.Internal (Config (..), Stats (..), defaultConfig)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main =
  defaultMain $
    testGroup
      "complexity (ADR 0007)"
      [ testCase "the committed benchmark parser is up to date" $ do
          src <- TIO.readFile "bench/Pathological.hpeg"
          committed <- B.readFile "bench/Conformance/Bench/Pathological.hs"
          let opts = Options {optSourceName = "bench/Pathological.hpeg", optOutputName = "bench/Conformance/Bench/Pathological.hs", optDebugEntry = True, optExports = Nothing}
          case generateFromSource opts src of
            Left ds -> assertFailure (show ds)
            Right code -> assertBool "regenerate with scripts/regen-fixtures.sh" (TE.encodeUtf8 code == committed)
      , testCase "the pathological grammar counts the b's" $
          fst (Pathological.peg'parseWith defaultConfig (input 5 7)) @?= Right 7
      , testProperty "evaluations are at most quadratic in the input length" $
          forAll ((,) <$> choose (1, 60) <*> choose (0, 60)) $ \(k, n) ->
            let evaluations = sum (M.elems (statsEvaluations (snd (Pathological.peg'parseWith defaultConfig {cfgCount = True} (input k n)))))
                len = k + n
             in counterexample (show evaluations) (evaluations <= 4 * (len + 2) * (len + 2))
      , testCase "the nested left recursion parsers are up to date" $
          mapM_
            ( \n -> do
                let src = "bench/NestedLR" <> show n <> ".hpeg"
                    out = "bench/Conformance/Bench/NestedLR" <> show n <> ".hs"
                grammar <- TIO.readFile src
                committed <- B.readFile out
                case generateFromSource (Options src out True Nothing) grammar of
                  Left ds -> assertFailure (show ds)
                  Right code -> assertBool ("regenerate " <> out) (TE.encodeUtf8 code == committed)
            )
            [2, 4, 8 :: Int]
      , testCase "nested left recursion: evaluations are linear in the nesting depth (ADR 0024)" $ do
          fst (NestedLR8.peg'parseWith defaultConfig (nested 3)) @?= Right ()
          -- Small depths, so that an exponential regression fails here
          -- instead of running for hours.
          let e1 = evalCount NestedLR8.peg'parseWith (nested 1)
              e2 = evalCount NestedLR8.peg'parseWith (nested 2)
          assertBool ("depth 1: " <> show e1 <> ", depth 2: " <> show e2) (fromIntegral e2 <= (2.5 :: Double) * fromIntegral e1)
      , testCase "nested left recursion: evaluations are linear in the number of levels (ADR 0024)" $ do
          let e2 = evalCount NestedLR2.peg'parseWith (nested 0)
              e4 = evalCount NestedLR4.peg'parseWith (nested 0)
              e8 = evalCount NestedLR8.peg'parseWith (nested 0)
          assertBool ("2: " <> show e2 <> ", 4: " <> show e4 <> ", 8: " <> show e8) (fromIntegral e8 <= (2.5 :: Double) * fromIntegral e4 && fromIntegral e4 <= (2.5 :: Double) * fromIntegral e2)
      , testCase "the pathological grammar is really quadratic" $ do
          let countFor m = sum (M.elems (statsEvaluations (snd (Pathological.peg'parseWith defaultConfig {cfgCount = True} (input m m)))))
          assertBool "doubling the input should roughly quadruple the evaluations" (countFor 200 > 3 * countFor 100)
      ]
  where
    input k n = T.replicate k (T.pack "a") <> T.replicate n (T.pack "b")
    nested d = T.replicate d (T.pack "(") <> T.pack "x" <> T.replicate d (T.pack ")")

evalCount :: (Config -> T.Text -> (Either ParseError (), Stats)) -> T.Text -> Int
evalCount run t = sum (M.elems (statsEvaluations (snd (run defaultConfig {cfgCount = True} t))))
