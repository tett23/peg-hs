module Main (main) where

import qualified Data.Text as T
import Data.Functor.Const (Const (..))
import Peg.Runtime.Internal
  ( ST, P, ParseError (parseErrorLabel), defaultConfig, runParser
  , andP, anyChar, choice, labeled, lit, many, skipMany, notP, predicate
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
  probe "anyChar" anyChar "x"
  probe "manyZero" (many (pure ()) *> lit "b" "b") "b"
  probe "skipManyZero" (skipMany (pure ()) *> lit "b" "b") "b"
  probe "manyFail" (many (lit "a" "a") *> lit "b" "b") "aaab"
  probe "skipManyFail" (skipMany (lit "a" "a") *> lit "b" "b") "aaab"
  probe "manyThrow" (many (labeled "inner" Nothing (lit "a" "a")) *> pure ()) "b"
  probe "skipManyThrow" (skipMany (labeled "inner" Nothing (lit "a" "a"))) "b"
  probe "manyLateZero" (many (choice [lit "a" "a", pure ()]) *> lit "b" "b") "aaab"
  probe "manyLateThrow" (many (choice [lit "a" "a", labeled "stop" Nothing (lit "c" "c")]) *> pure ()) "aaab"

-- Invariant 1: repetition stops at zero width, ordinary failure, and Throw.
