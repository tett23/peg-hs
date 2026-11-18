{-# LANGUAGE OverloadedStrings #-}

-- The public entries on the boundary rows of ADR 0097 (the table of its
-- invariants section). The printed lines, each named by its row's invariants,
-- are compared by check.sh with those of Boundary.lean; the other checks stop
-- with the name of the failed one.
module Main (main) where

import Control.Monad (forM_, unless)
import Data.Either (isRight)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Codegen (defaultOptions, generateWithWarnings, generationModule)
import Peg.Grammar (Diagnostic (..), Loc (..))
import Peg.Grammar.Parser (parseTops)
import System.Exit (die)

main :: IO ()
main = do
  let generate src = generateWithWarnings defaultOptions Nothing [] src >>= generationModule
      verdict r = if isRight r then "accept" else "reject"
      check name ok = unless ok (die (name ++ ": failed"))
  -- Row 1: the empty file has no top item, and generation reports the missing
  -- %module directive.
  putStrLn ("ADR 0097 I1, I2: empty file: parse " ++ verdict (parseTops ""))
  forM_ (either id (const []) (generate "")) $ \d ->
    putStrLn ("ADR 0097 I1, I2: empty file: generate " ++ T.unpack (diagMessage d))
  check "ADR 0097 I1: an empty file has no top item" (parseTops "" == Right [])
  -- Row 2: a minimal grammar, and the same with a trailing character.
  let valid = "%module M\nS <- 'a'\n"
      trailing = valid <> "]"
  putStrLn ("ADR 0097 I1, I2: minimal grammar: parse " ++ verdict (parseTops valid))
  putStrLn ("ADR 0097 I1, I2: trailing character: parse " ++ verdict (parseTops trailing))
  check "ADR 0097 I1: a minimal grammar generates a module" (isRight (generate valid))
  check "ADR 0097 I2: a trailing character gives a diagnostic and no module"
    (anyDiagnostic "" (generate trailing))
  -- Row 3: lookahead operators before one atom, at the depth limit and past it.
  let depth n = "%module M\nS <- " <> T.replicate n "&" <> "'a'\n"
  forM_ [0, 1, 254, 255, 256, 257, 258] $ \n -> do
    let result = parseTops (depth n)
    putStrLn ("ADR 0097 I1, I2: depth " ++ show n ++ ": " ++ verdict result)
    check ("ADR 0097 I2: depth " ++ show n ++ " is accepted or has the depth diagnostic")
      (isRight result || anyDiagnostic "deeper than 256" result)
  -- Row 4: one reference to an undefined rule.
  let undefinedReference = generate "%module M\nS <- Absent\n"
  forM_ (either id (const []) undefinedReference) $ \(Diagnostic (Loc f l c) m) ->
    putStrLn ("ADR 0097 I2: undefined reference: " ++ show f ++ ":" ++ show l ++ ":" ++ show c ++ " " ++ T.unpack m)
  check "ADR 0097 I2: an undefined reference gives a diagnostic and no module"
    (anyDiagnostic "undefined rule" undefinedReference)
  -- Rows 5 and 6 are checked with GHC (check-ghc-parser-trace.sh and check.sh).
  -- More inputs near the boundaries of the parser.
  let post n = "'a'" <> T.replicate n "?"
      grouped n = "(" <> post n <> " / " <> post n <> ")"
      wrapped n = "T<" <> post n <> ">"
  forM_ [(grouped 255, True), (grouped 256, False), (grouped 255 <> "?", False),
         (wrapped 255, True), (wrapped 256, False), ("&" <> post 254 <> "^label", True),
         ("&" <> post 255 <> "^label", False)] $ \(expr, accepted) -> do
    let result = parseTops ("%module M\nS <- " <> expr <> "\n")
    check ("ADR 0097 I1, I2: mixed nesting " ++ show expr)
      (if accepted then isRight result else anyDiagnostic "deeper than 256" result)
  forM_ [("'\\u{10FfFf}'", True), ("'\\u{110000}'", False), ("'\\u{}'", False),
         ("'\\u{D800}'", True), ("[z-a]", False), ("[a-a]", True), ("[\\-]", True)] $
    \(expr, accepted) -> check ("ADR 0097 I1: escape or character class " ++ show expr)
      (isRight (parseTops ("%module M\nS <- " <> expr <> "\n")) == accepted)
  let parameter raw = parseTops ("%module M\nS(" <> raw <> ") :: ()\nS <- 'a'\n")
  forM_ [("name", "expected a parameter of the form"), ("1name :: T", "expected a parameter of the form"),
         ("name ::  ", "expected a parameter type")] $ \(raw, message) ->
    check ("ADR 0097 I2: parameter diagnostic for " ++ show raw) (anyDiagnostic message (parameter raw))
  check "ADR 0097 I1: split only the first parameter separator" (isRight (parameter "  name' :: Foo :: Bar  "))
  forM_ [" ", "\t", "\xA0", "\x2003"] $ \space -> do
    let header ty = parseTops ("%module M\nS :: " <> ty <> "\nS <- 'a'\n")
        argument arg = parseTops ("%module M\nS <- F(" <> arg <> ")\n")
    check "ADR 0097 I1, I2: blank or trailing whitespace in type"
      (anyDiagnostic "expected a type" (header space) && isRight (header ("T" <> space)))
    check "ADR 0097 I1, I2: blank or nonblank argument"
      (anyDiagnostic "expected an argument" (argument space) && isRight (argument (space <> "x" <> space)))
  forM_ ["Peg.hpeg", "PegSyntax.hpeg"] $ \file -> do
    src <- TIO.readFile ("packages/peg-grammar/grammar/" ++ file)
    check ("ADR 0097 I1: self-hosted grammar " ++ file) (isRight (parseTops src) && isRight (generate src))

anyDiagnostic :: T.Text -> Either [Diagnostic] a -> Bool
anyDiagnostic needle = either (any (T.isInfixOf needle . diagMessage)) (const False)
