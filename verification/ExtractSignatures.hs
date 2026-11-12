{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- Emit only pairs of natural numbers, so hpeg input cannot introduce Lean code.
module Main (main) where

import Control.Monad (forM_, when)
import Data.Char (ord)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import System.Environment (getArgs)
import System.Exit (die)
import System.IO (hPutStrLn, stderr)

type Signature = (Integer, Int)

-- Nonzero digits in base 0x110001 give distinct names distinct numbers.
ruleNumber :: Text -> Integer
ruleNumber = T.foldl' (\n c -> n * 0x110001 + toInteger (ord c) + 1) 0

calls :: Expr -> Either String [Signature]
calls = \case
  ERef _ name args -> pure [(ruleNumber name, length args)]
  EGroup alts -> concat <$> traverse itemCalls alts
  EStar e -> calls e
  EPlus e -> calls e
  EOpt e -> calls e
  EAnd e -> calls e
  ENot e -> calls e
  ECapture e -> calls e
  ELabel _ e _ -> calls e
  EDiscard e -> calls e
  EAny -> pure []
  ELit _ _ -> pure []
  EClass _ _ -> pure []
  EPred _ _ -> pure []
  ETemplate {} -> Left "expected template expansion to remove every template call"

itemCalls :: [Item] -> Either String [Signature]
itemCalls items = concat <$> traverse (calls . itemExpr) items

main :: IO ()
main = do
  paths <- getArgs
  when (null paths) (die "pass at least one hpeg grammar")
  putStrLn "import Signatures"
  putStrLn "open PegHs.Signatures"
  forM_ (zip [1 :: Int ..] paths) $ \(index, path) -> do
    src <- TIO.readFile path
    grammar <- either (die . show) pure (parseGrammar src >>= expandTemplates)
    let rules = grammarRules grammar
        defs = [(ruleNumber (ruleName r), length (ruleParams r)) | r <- rules]
    refs <- either die pure $ concat <$> traverse (itemCalls . altItems) (concatMap ruleAlts rules)
    hPutStrLn stderr (path ++ ": " ++ show (length defs) ++ " definitions, " ++ show (length refs) ++ " calls")
    putStrLn ("namespace Grammar" ++ show index)
    putStrLn ("def definitions : List Signature := " ++ show defs)
    putStrLn ("def references : List Signature := " ++ show refs)
    putStrLn "theorem invariant2_all_calls_defined_with_expected_arity : WellFormed definitions references := by"
    putStrLn "  exact (invariant2_signatures _ _).mp (by decide)"
    putStrLn ("end Grammar" ++ show index)
