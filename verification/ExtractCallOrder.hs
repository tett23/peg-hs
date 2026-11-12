{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Main (main) where

import Control.Monad (forM_, when)
import Data.List (intercalate)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Parser (parseGrammar)
import System.Environment (getArgs)
import System.Exit (die)

-- These two fields only propose a certificate. Lean recomputes both
-- predicates from the emitted expression and verifies every same-offset edge.
data Projection = Projection
  { syntax :: String
  , nullable :: Bool
  , firstCalls :: [Int]
  }

project :: M.Map Text Int -> S.Set Int -> [[Item]] -> Either String Projection
project names known = alternatives
  where
    eps = Projection ".eps" True []
    token = Projection ".token" False []
    combine _ unit _ [] = unit
    combine op _ joinParts parts = foldr1 (combinePair op joinParts) parts
    combinePair op joinParts a b =
      let (empty, edges) = joinParts a b
       in Projection ("(." ++ op ++ " " ++ syntax a ++ " " ++ syntax b ++ ")") empty edges
    seqParts a b = (nullable a && nullable b, firstCalls a ++ [n | nullable a, n <- firstCalls b])
    altParts a b = (nullable a || nullable b, firstCalls a ++ firstCalls b)
    sequenceOf items = combine "seq" eps seqParts <$> traverse (expr . itemExpr) items
    alternatives alts = combine "alt" eps altParts <$> traverse sequenceOf alts
    wrapper op a = Projection ("(." ++ op ++ " " ++ syntax a ++ ")") True (firstCalls a)
    expr = \case
      EAny -> pure token
      EClass {} -> pure token
      ELit t _ -> pure (if t == "" then eps else token)
      ERef _ name _ -> case M.lookup name names of
        Nothing -> Left ("undefined reference in metagrammar: " ++ show name)
        Just n -> pure (Projection ("(.call " ++ show n ++ ")") (S.member n known) [n])
      EGroup alts -> alternatives alts
      EStar e -> wrapper "star" <$> expr e
      EPlus e -> do
        a <- expr e
        pure (combinePair "seq" seqParts a (wrapper "star" a))
      EOpt e -> (\a -> combinePair "alt" altParts a eps) <$> expr e
      EAnd e -> wrapper "look" <$> expr e
      ENot e -> wrapper "look" <$> expr e
      ECapture e -> expr e
      ELabel _ e _ -> expr e
      EDiscard e -> expr e
      EPred {} -> pure eps
      ETemplate {} -> Left "unexpanded template in metagrammar"

emit :: Int -> Grammar -> Either String [String]
emit index g = do
  let rs = grammarRules g
      names = M.fromList (zip (map ruleName rs) [0..])
      count = length rs
  when (not (null (grammarImports g)) || any (not . null . ruleTemplateParams) rs)
    (Left "expand libraries and templates before certifying a metagrammar")
  when (count /= M.size names || count == 0) (Left "duplicate or empty rules")
  let projections known = traverse (project names known . map altItems . ruleAlts) rs
      empties known = S.fromList . map fst . filter (nullable . snd) . zip [0..] <$> projections known
  known <- iterateM count empties S.empty
  bodies <- projections known
  let edges = map firstCalls bodies
      ranks = iterate (\r -> [maximum (0 : [1 + r !! n | n <- targets]) | targets <- edges])
                (replicate count (0 :: Int)) !! count
      rows = ["(" ++ syntax body ++ ", " ++ (if S.member n known then "true" else "false") ++ ", " ++ show rank ++ ")"
             | (n, (body, rank)) <- zip [0..] (zip bodies ranks)]
      ns = "Meta" ++ show index
  pure ["namespace " ++ ns,
        "def table : Array (Body × Bool × Nat) := #[\n" ++ intercalate ",\n" rows ++ "]",
        "def entry (n : Nat) := table[n]?.getD (.token, false, 0)",
        "def rules (n : Nat) := (entry n).1", "def known (n : Nat) := (entry n).2.1",
        "def rank (n : Nat) := (entry n).2.2",
        "theorem invariant1_checked : ∀ n, validRule known rank n (rules n) = true := by",
        "  have finite : ∀ i : Fin " ++ show count ++ ", validRule known rank i (rules i) = true := by decide",
        "  intro n; by_cases h : n < " ++ show count,
        "  · exact finite ⟨n,h⟩",
        "  · have miss : table[n]? = none := Array.getElem?_eq_none (by change " ++ show count ++ " ≤ n; omega)",
        "    simp [rules, known, rank, entry, miss, validRule, mayBeEmpty, beforeConsumption]",
        "theorem invariant1_same_position {caller callee} (h : Starts rules (rules caller) callee) : rank callee < rank caller :=",
        "  invariant1_rank_decreases invariant1_checked h",
        "theorem invariant1_recursive_calls_terminate : WellFounded (Nested rules) :=",
        "  invariant1_call_wellFounded invariant1_checked", "end " ++ ns]
  where
    iterateM 0 _ x = pure x
    iterateM k f x = f x >>= iterateM (k - 1) f

main :: IO ()
main = do
  paths <- getArgs
  when (null paths) (die "pass the actual metagrammar files")
  putStrLn "import CallOrder\nopen PegHs.CallOrder\nset_option maxRecDepth 16384\nset_option maxHeartbeats 12000000"
  forM_ (zip [1..] paths) $ \(index, path) -> do
    src <- TIO.readFile path
    either (die . ((path ++ ": ") ++)) (mapM_ putStrLn) $
      either (Left . show) Right (parseGrammar src) >>= emit index
