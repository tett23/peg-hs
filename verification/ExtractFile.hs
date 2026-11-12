{-# LANGUAGE OverloadedStrings #-}
-- Translate the recognition operators of the start production to Lean.
-- Emit fixed tokens only. Leave the two called rules as parameters.
module Main (main) where

import Control.Monad (forM_, when)
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

main :: IO ()
main = do
  paths <- getArgs
  when (null paths) (die "pass the metagrammar files")
  putStrLn "import File"
  putStrLn "open PegVerification PegVerification.File"
  forM_ paths $ \path -> do
    src <- TIO.readFile path
    grammar <- either (die . show) pure (parseGrammar src)
    let start = case grammarStart grammar of
          Just explicit -> Just (unLoc explicit)
          Nothing -> ruleName <$> listToMaybe (grammarRules grammar)
    when (start /= Just "File") (die (path ++ ": File must be the start rule"))
    tree <- either (die . ((path ++ ": ") ++)) pure $ case filter ((== "File") . ruleName) (grammarRules grammar) of
      [r] | null (ruleParams r), null (ruleTemplateParams r), [Alt _ items Nothing Nothing] <- ruleAlts r -> sequenceOf items
      _ -> Left "expected one parameterless File production"
    putStrLn ("example (ws item : Expr) : " ++ tree ++ " = fileExpr ws item := by rfl")
