{-# LANGUAGE OverloadedStrings #-}

-- Compare the depth predicate with the public hpeg parser at the file boundary.
module Main (main) where

import Control.Monad (forM_, unless)
import Data.Either (isRight)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Codegen (defaultOptions, generateWithWarnings, generationModule)
import Peg.Grammar (Diagnostic (..))
import Peg.Grammar.Parser (parseTops)
import System.Exit (die)

main :: IO ()
main = do
  let depth n = "%module M\nS <- " <> T.replicate n "&" <> "'a'\n"
  forM_ [0, 1, 254, 255, 256, 257, 258] $ \n -> do
    let result = parseTops (depth n)
    putStrLn (show n ++ " " ++ if isRight result then "accept" else "reject")
    unless (isRight result || anyDiagnostic "deeper than 256" result) $
      die ("invariant1: unexpected rejection at depth " ++ show n)
  unless (parseTops "" == Right []) $ die "invariant1: empty file"
  let valid = "%module M\nS <- 'a'\n"
      trailing = valid <> "]"
      generate src = generateWithWarnings defaultOptions Nothing [] src >>= generationModule
  unless (isRight (parseTops valid) && isRight (generate valid)) $ die "invariant1: single rule"
  unless (anyDiagnostic "" (parseTops trailing) && anyDiagnostic "" (generate trailing)) $
    die "invariant2: trailing input must give a diagnostic"
  unless (anyDiagnostic "missing %module" (generate "")) $ die "invariant2: empty module"
  unless (anyDiagnostic "undefined rule" (generate "%module M\nS <- Absent\n")) $
    die "invariant2: undefined reference"
  forM_ ["Peg.hpeg", "PegSyntax.hpeg"] $ \file -> do
    src <- TIO.readFile ("packages/peg-grammar/grammar/" ++ file)
    unless (isRight (parseTops src) && isRight (generate src)) $
      die ("invariant1: self-hosted grammar " ++ file)

anyDiagnostic :: T.Text -> Either [Diagnostic] a -> Bool
anyDiagnostic needle = either (any (T.isInfixOf needle . diagMessage)) (const False)
