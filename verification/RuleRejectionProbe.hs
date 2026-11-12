{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Text as T
import Peg.Codegen (defaultOptions, generateWithWarnings, generationModule)
import Peg.Grammar (Diagnostic (..))
import Peg.Grammar.Check (check)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import System.Exit (die)

checkRejected :: String -> T.Text -> T.Text -> IO ()
checkRejected label source needle = do
  let checked = parseGrammar source >>= expandTemplates >>= check
      generated = generateWithWarnings defaultOptions Nothing [] source >>= generationModule
  unless (either (not . null) (const False) checked) $
    die ("invariant2: " ++ label ++ " did not fail rule checking")
  case generated of
    Left ds | not (null ds) && any (T.isInfixOf needle . diagMessage) ds ->
      putStrLn (label ++ " " ++ show (length ds))
    Left ds -> die ("invariant2: " ++ label ++ " returned the wrong diagnostics: " ++ show ds)
    Right _ -> die ("invariant2: " ++ label ++ " generated a module")

checkAccepted :: String -> T.Text -> IO ()
checkAccepted label source =
  case generateWithWarnings defaultOptions Nothing [] source >>= generationModule of
    Right code | not (T.null code) -> putStrLn (label ++ " accepted")
    Right _ -> die ("invariant2: " ++ label ++ " generated empty output")
    Left ds -> die ("invariant2: " ++ label ++ " was unexpectedly rejected: " ++ show ds)

main :: IO ()
main = do
  checkRejected "invariant2_undefined" "%module M\nA :: ()\nA <- B { () }\n" "undefined rule B"
  checkRejected "invariant2_nullable_repeat" "%module M\nA :: ()\nA <- 'a'? * { () }\n"
    "the repeated expression can match the empty string"
  checkAccepted "invariant2_predicate_direct" "%module M\nA :: ()\nA <- &{ True } { () }\n"
  checkRejected "invariant2_predicate_star" "%module M\nA :: ()\nA <- (&{ True })* { () }\n"
    "the repeated expression can match the empty string"
  checkRejected "invariant2_predicate_plus" "%module M\nA :: ()\nA <- (&{ True })+ { () }\n"
    "the repeated expression can match the empty string"
