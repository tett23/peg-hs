-- | Benchmarks of ADR 0007. Compare results before and after a change on
-- the same machine; absolute numbers are not recorded.
module Main (main) where

import qualified Conformance.Bench.JsonCounted as JsonCounted
import qualified Conformance.Bench.JsonNomemo as JsonNomemo
import qualified Conformance.Bench.JsonSyntax as JsonSyntax
import Peg.Runtime.Syntax (syntaxRange)
import qualified Conformance.Bench.Pathological as Pathological
import Conformance.Json.Encode (encode)
import Conformance.Json.Parser (Value (..))
import qualified Conformance.Json.Parser as Json
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Ord (Down (..))
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
  case args of
    ["--memo-report"] -> memoReport
    ["--memory", variant, n] -> memory variant (read n)
    _ -> benchmarks

benchmarks :: IO ()
benchmarks = do
  jsonGrammar <- TIO.readFile "json/Json.peg"
  json <- evaluate (force (syntheticJson 10000))
  defaultMain
    [ bgroup
        "json"
        [ bench ("parse " <> show (T.length json) <> " characters") (whnf (either (const 0) size . Json.parse) json)
        , bench ("parse " <> show (T.length json) <> " characters with %nomemo") (whnf (either (const 0) (size . convertNomemo) . JsonNomemo.parse) json)
        , bench ("parse " <> show (T.length json) <> " characters with %syntax, typed entry") (whnf (either (const 0) (size . convertSyntax) . JsonSyntax.parse) json)
        , bench ("parse " <> show (T.length json) <> " characters with %syntax, tree entry") (whnf (either (const 0) (snd . syntaxRange) . JsonSyntax.parseSyntax) json)
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

-- Memo table sizes and live memory, as material for choosing %nomemo rules
-- (ADR 0006, ADR 0017).
memoReport :: IO ()
memoReport = withArgs [] $ do
  let small = syntheticJson 1000
      (_, st) = JsonCounted.peg'parseWith Rt.defaultConfig {cfgCount = True} small
  putStrLn ("json, " <> show (T.length small) <> " characters: memo entries by rule")
  forM_ (sortOn (Down . snd) (M.toList (statsEntriesByRule st))) $ \(rule, k) ->
    putStrLn ("  " <> T.unpack rule <> ": " <> show k)
  forM_ [100, 200, 400] $ \n -> do
    let (_, pst) = Pathological.peg'parseWith Rt.defaultConfig {cfgCount = True} (pathological n)
    putStrLn $
      "pathological, n = " <> show n <> ": evaluations " <> show (sum (statsEvaluations pst))
        <> ", memo entries at the end " <> show (statsMemoEntries pst)

-- The peak live memory of one parse. The peak is per process, so each
-- variant runs in its own process: --memory memoised|nomemo RECORDS.
memory :: String -> Int -> IO ()
memory variant n = withArgs [] $ do
  let input = syntheticJson n
      run = case variant of
        "nomemo" -> either (const 0) (size . convertNomemo) . JsonNomemo.parse
        "syntax" -> either (const 0) (size . convertSyntax) . JsonSyntax.parse
        "syntax-tree" -> either (const 0) (snd . syntaxRange) . JsonSyntax.parseSyntax
        _ -> either (const 0) size . Json.parse
  _ <- evaluate (T.length input)
  performMajorGC
  base <- getRTSStats
  r <- evaluate (run input)
  performMajorGC
  stats <- getRTSStats
  putStrLn $
    "json, " <> show (T.length input) <> " characters, " <> variant <> ": tree size " <> show r
      <> ", max live bytes " <> show (max_live_bytes stats)
      <> " (input and program before parsing: " <> show (max_live_bytes base) <> ")"


convertNomemo :: JsonNomemo.Value -> Value
convertNomemo v = case v of
  JsonNomemo.Null -> Null
  JsonNomemo.Bool b -> Bool b
  JsonNomemo.Number t -> Number t
  JsonNomemo.String t -> String t
  JsonNomemo.Array vs -> Array (map convertNomemo vs)
  JsonNomemo.Object ms -> Object [(k, convertNomemo x) | (k, x) <- ms]

convertSyntax :: JsonSyntax.Value -> Value
convertSyntax v = case v of
  JsonSyntax.Null -> Null
  JsonSyntax.Bool b -> Bool b
  JsonSyntax.Number t -> Number t
  JsonSyntax.String t -> String t
  JsonSyntax.Array vs -> Array (map convertSyntax vs)
  JsonSyntax.Object ms -> Object [(k, convertSyntax x) | (k, x) <- ms]
