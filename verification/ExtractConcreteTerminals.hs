{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}
module Main (main) where

import Control.Monad (forM_, when)
import Control.Monad.State.Strict (StateT, get, put, runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Char (ord)
import Data.List (intercalate)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Parser (parseGrammar)
import System.Environment (getArgs)
import System.Exit (die)

data Terminal = Lit [Char] | Cls [(Char, Char)] | Any

terminals :: Expr -> Either String [Terminal]
terminals = \case
  ELit value _ -> pure [Lit (T.unpack value)]
  EClass ranges _ -> pure [Cls ranges]
  EAny -> pure [Any]
  ERef {} -> pure []
  EGroup alts -> concat <$> traverse (fmap concat . traverse (terminals . itemExpr)) alts
  EStar e -> terminals e
  EPlus e -> terminals e
  EOpt e -> terminals e
  EAnd e -> terminals e
  ENot e -> terminals e
  ECapture e -> terminals e
  ELabel _ e _ -> terminals e
  EDiscard e -> terminals e
  EPred {} -> pure []
  ETemplate {} -> Left "unexpanded template in metagrammar"

predicateSites :: Expr -> [(Bool, T.Text)]
predicateSites = \case
  EPred polarity code -> [(polarity, unLoc code)]
  EGroup alts -> concatMap (concatMap (predicateSites . itemExpr)) alts
  EStar e -> predicateSites e
  EPlus e -> predicateSites e
  EOpt e -> predicateSites e
  EAnd e -> predicateSites e
  ENot e -> predicateSites e
  ECapture e -> predicateSites e
  ELabel _ e _ -> predicateSites e
  EDiscard e -> predicateSites e
  _ -> []

renderChar :: Char -> String
renderChar c = "Char.ofNat " ++ show (ord c)

renderString :: T.Text -> String
renderString value = "String.ofList [" ++ intercalate ", " (map renderChar (T.unpack value)) ++ "]"

renderTerminal :: Terminal -> String
renderTerminal = \case
  Lit chars -> "(.lit [" ++ intercalate ", " (map renderChar chars) ++ "])"
  Cls ranges -> "(.cls [" ++ intercalate ", " ["(" ++ renderChar a ++ ", " ++ renderChar b ++ ")" | (a, b) <- ranges] ++ "])"
  Any -> ".any"

type Build = StateT Int (Either String)

fresh :: Terminal -> Build Int
fresh _ = do
  index <- get
  put (index + 1)
  pure index

chain :: String -> String -> [String] -> String
chain _ unit [] = unit
chain op _ parts = foldr1 (\a b -> "(." ++ op ++ " " ++ a ++ " " ++ b ++ ")") parts

project :: M.Map T.Text Int -> Expr -> Build String
project names = \case
  ELit value _ -> do
    index <- fresh (Lit (T.unpack value))
    pure $ if T.null value then ".eps" else "(.terminal " ++ show index ++ ")"
  EClass ranges _ -> do
    index <- fresh (Cls ranges)
    pure ("(.terminal " ++ show index ++ ")")
  EAny -> do
    index <- fresh Any
    pure ("(.terminal " ++ show index ++ ")")
  ERef _ name _ -> case M.lookup name names of
    Just index -> pure ("(.call " ++ show index ++ ")")
    Nothing -> lift (Left ("undefined reference in metagrammar: " ++ show name))
  EGroup alts -> alternatives names alts
  EStar e -> (\a -> "(.star " ++ a ++ ")") <$> project names e
  EPlus e -> do
    a <- project names e
    pure ("(.seq " ++ a ++ " (.star " ++ a ++ "))")
  EOpt e -> (\a -> "(.alt " ++ a ++ " .eps)") <$> project names e
  EAnd e -> (\a -> "(.ahead " ++ a ++ ")") <$> project names e
  ENot e -> (\a -> "(.notAhead " ++ a ++ ")") <$> project names e
  ECapture e -> project names e
  ELabel _ e _ -> project names e
  EDiscard e -> project names e
  EPred {} -> pure ".eps"
  ETemplate {} -> lift (Left "unexpanded template in metagrammar")

type LabeledBuild = StateT (Int, Int) (Either String)

labeledProject :: M.Map T.Text Int -> M.Map T.Text T.Text -> Expr -> LabeledBuild String
labeledProject names messages = \case
  ELit value _ -> do
    (term, predSite) <- get
    put (term + 1, predSite)
    pure $ if T.null value then ".eps" else "(.terminal " ++ show term ++ ")"
  EClass {} -> freshTerminal
  EAny -> freshTerminal
  ERef _ name _ -> case M.lookup name names of
    Just index -> pure ("(.call " ++ show index ++ ")")
    Nothing -> lift (Left ("undefined reference in metagrammar: " ++ show name))
  EGroup alts -> labeledAlternatives names messages alts
  EStar e -> wrap "star" e
  EPlus e -> do
    a <- labeledProject names messages e
    pure ("(.seq " ++ a ++ " (.star " ++ a ++ "))")
  EOpt e -> do
    a <- labeledProject names messages e
    pure ("(.alt " ++ a ++ " .eps)")
  EAnd e -> wrap "ahead" e
  ENot e -> wrap "notAhead" e
  ECapture e -> labeledProject names messages e
  ELabel _ e label -> do
    a <- labeledProject names messages e
    let rendered = case M.lookup label messages of
          Nothing -> "none"
          Just value -> "(some (" ++ renderString value ++ "))"
    pure ("(.label (" ++ renderString label ++ ") " ++ rendered ++ " " ++ a ++ ")")
  EDiscard e -> labeledProject names messages e
  EPred polarity _ -> do
    (term, predSite) <- get
    put (term, predSite + 1)
    pure ("(.predicate " ++ show predSite ++ " " ++ (if polarity then "true" else "false") ++ ")")
  ETemplate {} -> lift (Left "unexpanded template in metagrammar")
  where
    freshTerminal = do
      (term, predSite) <- get
      put (term + 1, predSite)
      pure ("(.terminal " ++ show term ++ ")")
    wrap constructor e = do
      a <- labeledProject names messages e
      pure ("(." ++ constructor ++ " " ++ a ++ ")")

labeledAlternatives :: M.Map T.Text Int -> M.Map T.Text T.Text -> [[Item]] -> LabeledBuild String
labeledAlternatives names messages alts = do
  parts <- traverse (fmap (chain "seq" ".eps") . traverse (labeledProject names messages . itemExpr)) alts
  pure (chain "alt" ".eps" parts)

alternatives :: M.Map T.Text Int -> [[Item]] -> Build String
alternatives names alts = do
  parts <- traverse (fmap (chain "seq" ".eps") . traverse (project names . itemExpr)) alts
  pure (chain "alt" ".eps" parts)

emit :: Int -> Grammar -> Either String [String]
emit index g = do
  let rs = grammarRules g
      names = map ruleName rs
      count = length rs
      nameToIndex = M.fromList (zip names [0 ..])
  when (null rs || length rs /= S.size (S.fromList names) || not (null (grammarImports g)) ||
        any (not . null . ruleTemplateParams) rs)
    (Left "duplicate/empty rules, imports, or unexpanded templates in metagrammar")
  rows <- traverse (traverse (terminals . itemExpr) . concatMap altItems . ruleAlts) rs
  (bodies, assigned) <- runStateT (traverse (alternatives nameToIndex . map altItems . ruleAlts) rs) 0
  let messages = M.fromList [(unLoc name, unLoc msg) | (name, msg) <- grammarMessages g]
  (labeledBodies, (labeledTerms, labeledPredicates)) <-
    runStateT (traverse (labeledAlternatives nameToIndex messages . map altItems . ruleAlts) rs) (0, 0)
  let numbered = [(rule, term) | (rule, groups) <- zip [0 :: Int ..] rows, term <- concat groups]
      predicateRows =
        [(ruleName r, polarity, source) | r <- rs,
          a <- ruleAlts r, item <- altItems a,
          (polarity, source) <- predicateSites (itemExpr item)]
      literals = length [() | (_, Lit _) <- numbered]
      classes = length [() | (_, Cls _) <- numbered]
      anys = length [() | (_, Any) <- numbered]
      ns = "MetaTerminal" ++ show index
      table = ["(" ++ show rule ++ ", " ++ renderTerminal term ++ ")" | (rule, term) <- numbered]
  when (assigned /= length numbered || labeledTerms /= assigned || labeledPredicates /= length predicateRows)
    (Left "site numbering differs from source extraction")
  pure ["namespace " ++ ns,
        "def table : Array (Nat × Terminal) := #[\n" ++ intercalate ",\n" table ++ "]",
        "theorem invariant1_terminal_count : table.size = " ++ show (length numbered) ++ " := by decide",
        "theorem invariant1_all_match (i : Fin table.size) (xs ys : List Char) :",
        "    matchTerm table[i].2 xs = some ys ↔ Matches table[i].2 xs ys :=",
        "  invariant1_matchTerm_iff _ _ _",
        "theorem invariant1_all_reject (i : Fin table.size) (xs : List Char) :",
        "    matchTerm table[i].2 xs = none ↔ ¬∃ ys, Matches table[i].2 xs ys :=",
        "  invariant1_reject_iff _ _",
        "theorem invariant1_all_at (i : Fin table.size) (input : List Char) (start finish : Nat) :",
        "    matchAt table[i].2 input start = some finish ↔ MatchesAt table[i].2 input start finish :=",
        "  invariant1_matchAt_iff _ _ _ _",
        "theorem invariant1_all_at_reject (i : Fin table.size) (input : List Char) (start : Nat) :",
        "    matchAt table[i].2 input start = none ↔ ¬∃ finish, MatchesAt table[i].2 input start finish :=",
        "  invariant1_matchAt_reject _ _ _",
        "theorem invariant1_all_at_bounds (i : Fin table.size) (input : List Char) (start finish : Nat)",
        "    (accepted : matchAt table[i].2 input start = some finish) :",
        "    start ≤ finish ∧ finish ≤ input.length :=",
        "  invariant1_matchAt_bounds accepted",
        "theorem invariant1_all_oracle (i : Fin table.size) (input : List Char) (remaining rest : Nat) :",
        "    terminalOracle table[i].2 input remaining = some rest ↔",
        "      TerminalStep table[i].2 input remaining rest :=",
        "  invariant1_terminalOracle_iff _ _ _ _",
        "theorem invariant1_all_oracle_reject (i : Fin table.size) (input : List Char) (remaining : Nat) :",
        "    terminalOracle table[i].2 input remaining = none ↔",
        "      ¬∃ rest, TerminalStep table[i].2 input remaining rest :=",
        "  invariant1_terminalOracle_reject _ _ _",
        "#print axioms invariant1_all_match",
        "#print axioms invariant1_all_reject",
        "#print axioms invariant1_all_at",
        "#print axioms invariant1_all_at_reject",
        "#print axioms invariant1_all_at_bounds",
        "#print axioms invariant1_all_oracle",
        "#print axioms invariant1_all_oracle_reject",
        "def bodyTable : Array Body := #[\n" ++ intercalate ",\n" bodies ++ "]",
        "def body (n : Nat) := bodyTable[n]?.getD (.terminal 0)",
        "theorem invariant1_body_count : bodyTable.size = " ++ show count ++ " := by decide",
        "theorem invariant1_erasure : ∀ i : Fin " ++ show count ++ ",",
        "    PegHs.ConcreteTerminalBody.erase (body i) = Meta" ++ show index ++ ".rules i := by decide",
        "theorem invariant1_erasure_all (n : Nat) :",
        "    PegHs.ConcreteTerminalBody.erase (body n) = Meta" ++ show index ++ ".rules n := by",
        "  by_cases h : n < " ++ show count,
        "  · exact invariant1_erasure ⟨n, h⟩",
        "  · have bodyMiss : bodyTable[n]? = none := Array.getElem?_eq_none (by change " ++ show count ++ " ≤ n; omega)",
        "    have callMiss : Meta" ++ show index ++ ".table[n]? = none := Array.getElem?_eq_none (by change " ++ show count ++ " ≤ n; omega)",
        "    simp [body, bodyMiss, Meta" ++ show index ++ ".rules, Meta" ++ show index ++ ".entry, callMiss,",
        "      PegHs.ConcreteTerminalBody.erase]",
        "theorem invariant1_checked : ∀ n,",
        "    PegHs.CallOrder.validRule Meta" ++ show index ++ ".known Meta" ++ show index ++ ".rank n",
        "      (PegHs.ConcreteTerminalBody.erase (body n)) = true := by",
        "  intro n",
        "  rw [invariant1_erasure_all]",
        "  exact Meta" ++ show index ++ ".invariant1_checked n",
        "theorem invariant1_terminal_ids : ∀ i : Fin " ++ show count ++ ",",
        "    (PegHs.ConcreteTerminalBody.terminalIds (body i)).all (fun id => id < table.size) = true := by decide",
        "def termById (id : Nat) : Option Terminal := (table[id]?).map Prod.snd",
        "def runConcrete (input : List Char) (fuel rule : Nat) : Option PegHs.RecursiveEval.Result :=",
        "  PegHs.ConcreteTerminalBody.runFuel body termById input fuel (body rule) input.length",
        "theorem invariant1_runConcrete_sound (input : List Char) (fuel rule : Nat)",
        "    (result : PegHs.RecursiveEval.Result)",
        "    (h : runConcrete input fuel rule = some result) :",
        "    PegHs.ConcreteTerminalBody.Derives body termById input (body rule) input.length result :=",
        "  PegHs.ConcreteTerminalBody.invariant1_runFuel_sound h",
        "theorem invariant1_runConcrete_total (input : List Char) (rule : Nat) :",
        "    ∃ fuel result, runConcrete input fuel rule = some result := by",
        "  simpa [runConcrete] using",
        "    (PegHs.ConcreteTerminalBody.invariant1_rule_executable",
        "      (rules := body) (terms := termById) (input := input)",
        "      invariant1_checked (input.length, rule))",
        "#print axioms invariant1_erasure",
        "#print axioms invariant1_erasure_all",
        "#print axioms invariant1_checked",
        "#print axioms invariant1_terminal_ids",
        "#print axioms invariant1_runConcrete_sound",
        "#print axioms invariant1_runConcrete_total",
        "def predicateSites : Array (String × Bool × String) := #[" ++
          intercalate ", " ["(" ++ renderString rule ++ ", " ++
            (if polarity then "true" else "false") ++ ", " ++ renderString source ++ ")"
            | (rule, polarity, source) <- predicateRows] ++ "]",
        "theorem invariant1_predicate_count : predicateSites.size = " ++ show labeledPredicates ++ " := by decide",
        "def labeledBodyTable : Array PegHs.LabeledConcreteBody.Body := #[\n" ++
          intercalate ",\n" labeledBodies ++ "]",
        "def labeledBody (n : Nat) := labeledBodyTable[n]?.getD (.terminal 0)",
        "theorem invariant1_labeled_body_count : labeledBodyTable.size = " ++ show count ++ " := by decide",
        "theorem invariant1_labeled_erasure : ∀ i : Fin " ++ show count ++ ",",
        "    PegHs.LabeledConcreteBody.erase (labeledBody i) = Meta" ++ show index ++ ".rules i := by decide",
        "theorem invariant1_labeled_erasure_all (n : Nat) :",
        "    PegHs.LabeledConcreteBody.erase (labeledBody n) = Meta" ++ show index ++ ".rules n := by",
        "  by_cases h : n < " ++ show count,
        "  · exact invariant1_labeled_erasure ⟨n, h⟩",
        "  · have bodyMiss : labeledBodyTable[n]? = none := Array.getElem?_eq_none (by change " ++ show count ++ " ≤ n; omega)",
        "    have callMiss : Meta" ++ show index ++ ".table[n]? = none := Array.getElem?_eq_none (by change " ++ show count ++ " ≤ n; omega)",
        "    simp [labeledBody, bodyMiss, Meta" ++ show index ++ ".rules, Meta" ++ show index ++ ".entry, callMiss,",
        "      PegHs.LabeledConcreteBody.erase]",
        "theorem invariant1_labeled_checked : ∀ n,",
        "    PegHs.CallOrder.validRule Meta" ++ show index ++ ".known Meta" ++ show index ++ ".rank n",
        "      (PegHs.LabeledConcreteBody.erase (labeledBody n)) = true := by",
        "  intro n",
        "  rw [invariant1_labeled_erasure_all]",
        "  exact Meta" ++ show index ++ ".invariant1_checked n",
        "def runLabeled (oracle : Nat → Nat → Bool) (input : List Char)",
        "    (fuel rule : Nat) : Option PegHs.LabeledConcreteBody.Result :=",
        "  PegHs.LabeledConcreteBody.runFuel labeledBody termById oracle input",
        "    fuel (labeledBody rule) input.length",
        "theorem invariant1_runLabeled_total (oracle : Nat → Nat → Bool)",
        "    (input : List Char) (rule : Nat) :",
        "    ∃ fuel result, runLabeled oracle input fuel rule = some result := by",
        "  simpa [runLabeled] using",
        "    (PegHs.LabeledConcreteBody.invariant1_rule_executable",
        "      (rules := labeledBody) (terms := termById) (oracle := oracle)",
        "      (input := input) invariant1_labeled_checked (input.length, rule))",
        "#print axioms invariant1_labeled_erasure",
        "#print axioms invariant1_labeled_erasure_all",
        "#print axioms invariant1_labeled_checked",
        "#print axioms invariant1_runLabeled_total",
        "end " ++ ns,
        "-- counts " ++ show literals ++ " literal, " ++ show classes ++ " class, " ++ show anys ++ " any"]

main :: IO ()
main = do
  paths <- getArgs
  when (null paths) (die "pass the actual metagrammar files")
  putStrLn "import ConcreteTerminalBody\nimport LabeledConcreteBody\nimport CallTables\nopen PegHs.ConcreteTerminal PegHs.ConcreteTerminalBody\nset_option maxRecDepth 16384\nset_option maxHeartbeats 12000000"
  forM_ (zip [1 ..] paths) $ \(index, path) -> do
    src <- TIO.readFile path
    either (die . ((path ++ ": ") ++)) (mapM_ putStrLn) $
      either (Left . show) Right (parseGrammar src) >>= emit index
