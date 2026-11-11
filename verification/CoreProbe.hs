module Main (main) where

import qualified Data.Text as T
import Data.Functor.Const (Const (..))
import Peg.Runtime.Internal
  ( ST, P, ParseError (parseErrorLabel), defaultConfig, runParser
  , andP, choice, labeled, lit, notP, predicate
  )

mkStore :: forall s. ST s (Const () s)
mkStore = pure (Const ())

probe :: String -> (forall s. P (Const () s) s ()) -> String -> IO ()
probe name parser input =
  case fst (runParser defaultConfig mkStore parser (T.pack input)) of
    Right () -> putStrLn (name ++ " ok")
    Left err -> putStrLn (name ++ " " ++ maybe "fail" (("throw:" ++) . T.unpack) (parseErrorLabel err))

main :: IO ()
main = do
  probe "choiceThrow" (choice [labeled "inner" Nothing (lit "a" "a"), lit "b" "b"]) "b"
  probe "aheadLabel" (andP (labeled "inner" Nothing (lit "a" "a"))) "b"
  probe "nestedLabel" (labeled "outer" Nothing (labeled "inner" Nothing (lit "a" "a"))) "b"
  probe "normalChoice" (choice [lit "a" "a", lit "b" "b"]) "b"
  probe "notLabel" (notP (labeled "inner" Nothing (lit "a" "a")) *> lit "b" "b") "b"
  probe "predicate" (predicate (\_ -> True)) ""
