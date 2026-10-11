-- | Benchmarks of ADR 0007. Compare results before and after a change on
-- the same machine; absolute numbers are not recorded.
module Main (main) where

import qualified Conformance.Bench.Pathological as Pathological
import Conformance.Json.Encode (encode)
import Conformance.Json.Parser (Value (..))
import qualified Conformance.Json.Parser as Json
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_)
import Criterion.Main
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import GHC.Stats (RTSStats (..), getRTSStats)
import Peg.Codegen (defaultOptions, generateFromSource)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Runtime.Internal (Config (..), Stats (..))
import qualified Peg.Runtime.Internal as Rt
import System.Environment (getArgs, withArgs)
import System.Mem (performMajorGC)

-- A deterministic JSON document of roughly the given number of records.
syntheticJson :: Int -> Text
syntheticJson n = encode (Array [record i | i <- [1 .. n]])
  where
    record i =
      Object
        [ (T.pack "id", Number (T.pack (show i)))
        , (T.pack "name", String (T.pack ("item " <> show i <> " \x3042\x3044\x3046")))
        , (T.pack "tags", Array [String (T.pack "a"), String (T.pack "b"), Null, Bool (even i)])
        , (T.pack "score", Number (T.pack (show i <> ".5e-3")))
        ]

-- Force the whole tree.
size :: Value -> Int
size v = case v of
  Null -> 1
  Bool b -> if b then 1 else 1
  Number t -> T.length t
  String t -> T.length t
  Array vs -> 1 + sum (map size vs)
  Object ms -> 1 + sum [T.length k + size x | (k, x) <- ms]

pathological :: Int -> Text
pathological n = T.replicate n (T.pack "a") <> T.replicate n (T.pack "b")

main :: IO ()
main = do
  args <- getArgs
  if "--memo-report" `elem` args then memoReport else benchmarks

benchmarks :: IO ()
benchmarks = do
  jsonGrammar <- TIO.readFile "json/Json.peg"
  json <- evaluate (force (syntheticJson 10000))
  defaultMain
    [ bgroup
        "json"
        [ bench ("parse " <> show (T.length json) <> " characters") (whnf (either (const 0) size . Json.parse) json)
        ]
    , bgroup
        "left recursion (pathological)"
        [ bench ("n = " <> show n) (whnf (fst . Pathological.peg'parseWith Rt.defaultConfig) (pathological n))
        | n <- [100, 200, 400]
        ]
    , bgroup
        "generator"
        [ bench "parse Json.peg" (whnf (either (const 0) (length . show) . parseGrammar) jsonGrammar)
        , bench "generate Json.peg" (whnf (either (const 0) T.length . generateFromSource defaultOptions) jsonGrammar)
        ]
    ]

-- Memo table sizes and live memory, as material for the %nomemo decision
-- (ADR 0006).
memoReport :: IO ()
memoReport = withArgs [] $ do
  forM_ [1000, 10000] $ \n -> do
    let input = syntheticJson n
    _ <- evaluate (T.length input)
    performMajorGC
    before <- getRTSStats
    r <- evaluate (either (const 0) size (Json.parse input))
    performMajorGC
    after <- getRTSStats
    putStrLn $
      "json, " <> show (T.length input) <> " characters: tree size " <> show r
        <> ", max live bytes " <> show (max_live_bytes after)
        <> " (before " <> show (max_live_bytes before) <> ")"
  forM_ [100, 200, 400] $ \n -> do
    let (_, st) = Pathological.peg'parseWith Rt.defaultConfig {cfgCount = True} (pathological n)
    putStrLn $
      "pathological, n = " <> show n <> ": evaluations " <> show (sum (statsEvaluations st))
        <> ", memo entries at the end " <> show (statsMemoEntries st)
