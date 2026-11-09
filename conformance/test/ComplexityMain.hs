-- | Evaluation counts of left recursion stay within the quadratic bound of
-- ADR 0007, and the committed benchmark parser is up to date.
module Main (main) where

import qualified Conformance.Bench.NestedLR2 as NestedLR2
import qualified Conformance.Bench.NestedLR4 as NestedLR4
import qualified Conformance.Bench.NestedLR8 as NestedLR8
import qualified Conformance.Bench.Pathological as Pathological
import qualified Conformance.Bench.PegCounted as PegCounted
import Peg.Runtime (ParseError (..))
import qualified Data.ByteString as B
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Codegen (Options (..), generateFromSource)
import Peg.Grammar.Check (check)
import Peg.Grammar.Interpret (Interpreter, interpretWith, interpreter)
import Peg.Grammar.Parser (parseGrammar)
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
      , testCase "the counted parser of the notation is up to date" $ do
          src <- TIO.readFile "bench/PegCounted.txt"
          committed <- B.readFile "bench/Conformance/Bench/PegCounted.hs"
          case generateFromSource (Options "bench/PegCounted.txt" "bench/Conformance/Bench/PegCounted.hs" True Nothing) src of
            Left ds -> assertFailure (show ds)
            Right code -> assertBool "regenerate with scripts/regen-fixtures.sh" (TE.encodeUtf8 code == committed)
      , testCase "a nesting of 100,000 levels is rejected in evaluations linear in its length (ADR 0080)" $ do
          let run n = PegCounted.peg'parseWith defaultConfig {cfgCount = True} (deepGrammar n)
              count n = sum (M.elems (statsEvaluations (snd (run n))))
              e1 = count 50000
              e2 = count 100000
          fmap parseErrorLabel (either Just (const Nothing) (fst (run 100000))) @?= Just (Just (T.pack "nest"))
          assertBool ("50,000: " <> show e1 <> ", 100,000: " <> show e2) (fromIntegral e2 <= (2.5 :: Double) * fromIntegral e1)
          assertBool ("100,000: " <> show e2) (e2 <= 10 * T.length (deepGrammar 100000))
      , testGroup
          "the interpreter evaluates the rules as the generated parsers (ADR 0090)"
          ( [ testCase "Pathological" $ do
                ip <- interpreterOf "bench/Pathological.hpeg"
                sameCounts ip Pathological.peg'parseWith [input k n | (k, n) <- [(5, 7), (1, 0), (0, 3), (10, 20), (60, 60), (100, 100), (200, 200)]]
            ]
              ++ [ testCase ("NestedLR" <> show n) $ do
                    ip <- interpreterOf ("bench/NestedLR" <> show n <> ".hpeg")
                    sameCounts ip run (map nested [0 .. 3] ++ [T.pack "x+x*x^(x)", T.pack "(x"])
                 | (n, run) <- [(2 :: Int, NestedLR2.peg'parseWith), (4, NestedLR4.peg'parseWith), (8, NestedLR8.peg'parseWith)]
                 ]
          )
      , testCase "the pathological grammar is really quadratic" $ do
          let countFor m = sum (M.elems (statsEvaluations (snd (Pathological.peg'parseWith defaultConfig {cfgCount = True} (input m m)))))
          assertBool "doubling the input should roughly quadruple the evaluations" (countFor 200 > 3 * countFor 100)
      ]
  where
    input k n = T.replicate k (T.pack "a") <> T.replicate n (T.pack "b")
    nested d = T.replicate d (T.pack "(") <> T.pack "x" <> T.replicate d (T.pack ")")
    -- A grammar whose expression nests groups n levels deep (ADR 0080).
    deepGrammar n = T.pack "%module M\nS <- " <> T.replicate n (T.pack "(") <> T.pack "'a'" <> T.replicate n (T.pack ")") <> T.pack "\n"

-- The interpreter of a grammar file (ADR 0090).
interpreterOf :: FilePath -> IO Interpreter
interpreterOf file = do
  src <- TIO.readFile file
  case parseGrammar src >>= \g -> check g >>= interpreter g of
    Left ds -> assertFailure (show ds) >> error "unreachable"
    Right ip -> pure ip

-- The same evaluations of each rule at each offset, and the same result.
sameCounts :: Interpreter -> (Config -> T.Text -> (Either ParseError a, Stats)) -> [T.Text] -> Assertion
sameCounts ip run inputs =
  mapM_
    ( \t -> do
        let (r, st) = run defaultConfig {cfgCount = True} t
            (r', st') = interpretWith defaultConfig {cfgCount = True} ip Nothing t
        (t, either Left (const (Right ())) r', statsEvaluations st') @?= (t, either Left (const (Right ())) r, statsEvaluations st)
    )
    inputs

evalCount :: (Config -> T.Text -> (Either ParseError (), Stats)) -> T.Text -> Int
evalCount run t = sum (M.elems (statsEvaluations (snd (run defaultConfig {cfgCount = True} t))))
