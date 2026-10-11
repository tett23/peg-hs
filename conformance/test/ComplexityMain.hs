-- | Evaluation counts of left recursion stay within the quadratic bound of
-- ADR 0007, and the committed benchmark parser is up to date.
module Main (main) where

import qualified Conformance.Bench.Pathological as Pathological
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
          src <- TIO.readFile "bench/Pathological.peg"
          committed <- B.readFile "bench/Conformance/Bench/Pathological.hs"
          let opts = Options {optSourceName = "bench/Pathological.peg", optOutputName = "bench/Conformance/Bench/Pathological.hs", optDebugEntry = True}
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
      , testCase "the pathological grammar is really quadratic" $ do
          let countFor m = sum (M.elems (statsEvaluations (snd (Pathological.peg'parseWith defaultConfig {cfgCount = True} (input m m)))))
          assertBool "doubling the input should roughly quadruple the evaluations" (countFor 200 > 3 * countFor 100)
      ]
  where
    input k n = T.replicate k (T.pack "a") <> T.replicate n (T.pack "b")
