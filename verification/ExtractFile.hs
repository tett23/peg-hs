{-# LANGUAGE OverloadedStrings #-}
-- Translate the recognition operators of the start production to Lean.
-- Also specialize its empty-input premises to the actual lexical and top-level rules.
module Main (main) where

import Control.Monad (forM_, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.Char (ord)
import Data.List (inits, intercalate)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (listToMaybe)
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Parser (parseGrammar)
import System.Environment (getArgs)
import System.Exit (die)

expression :: Expr -> Either String String
expression expr = case expr of
  ERef _ "Ws" [] -> Right "ws"
  ERef _ "TopItem" [] -> Right "item"
  EAny -> Right ".any"
  EStar e -> unary ".many" e
  ENot e -> unary ".notAhead" e
  ELabel _ e "top" -> unary ".label \"top\"" e
  EGroup [items] -> sequenceOf items
  _ -> Left "unsupported expression in File"
  where
    unary op e = (\body -> "(" ++ op ++ " " ++ body ++ ")") <$> expression e

sequenceOf :: [Item] -> Either String String
sequenceOf items = do
  parts <- traverse translateItem items
  case parts of
    [] -> Left "empty sequence in File"
    p : ps -> Right (foldr1 (\a b -> "(.seq " ++ a ++ " " ++ b ++ ")") (p : ps))
  where
    translateItem (Item _ Nothing e) = expression e
    translateItem _ = Left "unsupported binding in File"

-- Emit local definitions in dependency order. An unexpanded call or semantic
-- predicate gets its own parameter, so the proof cannot rely on its result.
rules :: [Text]
rules = ["Here", "SpaceChar", "Comment", "Ws", "IdentStart", "Ident",
         "Verbatim", "Directive", "Declaration", "TopOne", "TopItem"]

type Emit = StateT Int (Either String)

unknownExpr :: Emit String
unknownExpr = do
  n <- get
  put (n + 1)
  pure ("(rest " ++ show n ++ ")")

combine :: String -> String -> [String] -> String
combine _ unit [] = unit
combine op _ xs = foldr1 (\a b -> "(" ++ op ++ " " ++ a ++ " " ++ b ++ ")") xs

-- Natural-number literals are the only input-derived tokens in generated Lean.
character :: Char -> String
character c = "(Char.ofNat " ++ show (ord c) ++ ")"

recognition :: [Text] -> Expr -> Emit String
recognition earlier expr = case expr of
  ERef _ name [] | name `elem` earlier -> pure ("(rule" ++ T.unpack name ++ " rest)")
  ERef _ name _ | name `elem` rules -> lift (Left "unsupported forward or parameterized rule call")
  ERef {} -> unknownExpr
  EPred {} -> unknownExpr
  EAny -> pure ".any"
  ELit value _ -> pure (combine ".seq" "(.predicate true)" ["(.char " ++ character c ++ ")" | c <- T.unpack value])
  ECapture e -> rec e
  EGroup alts -> combine ".choice" "(.predicate false)" <$> traverse items alts
  ELabel _ e label -> do
    body <- rec e
    let chars = map character (T.unpack label)
    pure ("(.label (String.ofList [" ++ intercalate ", " chars ++ "]) " ++ body ++ ")")
  EAnd e -> unary ".ahead" e
  ENot e -> unary ".notAhead" e
  EStar e -> unary ".many" e
  EOpt e -> do
    body <- rec e
    pure ("(.choice " ++ body ++ " (.predicate true))")
  _ -> lift (Left "unsupported expression in an expanded recognition rule")
  where
    rec = recognition earlier
    unary op e = (\body -> "(" ++ op ++ " " ++ body ++ ")") <$> rec e
    items = fmap (combine ".seq" "(.predicate true)") . traverse (rec . itemExpr)

emitRules :: Grammar -> Either String [String]
emitRules grammar = flip evalStateT 0 $ sequence
  [ case filter ((== name) . ruleName) (grammarRules grammar) of
      [r] | null (ruleParams r), null (ruleTemplateParams r) -> do
        alternatives <- traverse (traverse (recognition earlier . itemExpr) . altItems) (ruleAlts r)
        let body = combine ".choice" "(.predicate false)" (map (combine ".seq" "(.predicate true)") alternatives)
        pure ("def rule" ++ T.unpack name ++ " (rest : Nat → Expr) : Expr := " ++ body)
      _ -> lift (Left ("expected one parameterless rule " ++ T.unpack name))
  | (earlier, name) <- zip (inits rules) rules ]

main :: IO ()
main = do
  paths <- getArgs
  when (null paths) (die "pass the metagrammar files")
  putStrLn "import Consumption"
  putStrLn "open PegVerification PegVerification.File"
  putStrLn "set_option linter.unusedVariables false"
  forM_ (zip [1 :: Int ..] paths) $ \(index, path) -> do
    src <- TIO.readFile path
    grammar <- either (die . show) pure (parseGrammar src)
    let start = case grammarStart grammar of
          Just explicit -> Just (unLoc explicit)
          Nothing -> ruleName <$> listToMaybe (grammarRules grammar)
    when (start /= Just "File") (die (path ++ ": File must be the start rule"))
    tree <- either (die . ((path ++ ": ") ++)) pure $ case filter ((== "File") . ruleName) (grammarRules grammar) of
      [r] | null (ruleParams r), null (ruleTemplateParams r), [Alt _ items Nothing Nothing] <- ruleAlts r -> sequenceOf items
      _ -> Left "expected one parameterless File production"
    let namespaceName = "Grammar" ++ show index
    putStrLn ("namespace " ++ namespaceName)
    definitions <- either (die . ((path ++ ": ") ++)) pure (emitRules grammar)
    mapM_ putStrLn definitions
    putStrLn ("def start (ws item : Expr) : Expr := " ++ tree)
    putStrLn "example (ws item : Expr) : start ws item = fileExpr ws item := by rfl"
    putStrLn "theorem invariant1_topItem_empty (rest : Nat → Expr) : run (ruleTopItem rest) [] = .error none := by rfl"
    putStrLn "theorem invariant1_ws_empty (rest : Nat → Expr) : run (ruleWs rest) [] = .ok [] := by rfl"
    putStrLn "theorem invariant1_file_empty (rest : Nat → Expr) : run (start (ruleWs rest) (ruleTopItem rest)) [] = .ok [] := by rfl"
    putStrLn "theorem invariant1_file (rest : Nat → Expr) (src : List Char) :"
    putStrLn "  run (start (ruleWs rest) (ruleTopItem rest)) src = .ok [] ↔"
    putStrLn "    ∃ xs, Eval (ruleWs rest) src (.ok xs) ∧ PrefixItems (ruleTopItem rest) xs := by"
    putStrLn "  simp only [← invariant1_file_items_prefix]"
    putStrLn "  exact invariant1_file_derivation _ _ src (invariant1_topItem_empty rest)"
    putStrLn ("end " ++ namespaceName)
