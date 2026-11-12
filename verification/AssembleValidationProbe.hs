{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as T
import Peg.Codegen (generateWithWarnings, defaultOptions)
import Peg.Grammar (Diagnostic (..), Loc (..), Located (..), Alt (..), TemplateParam (..))
import Peg.Grammar.Assemble (Top (..), assemble)
import System.Exit (die)

l :: Loc
l = Loc 0 1 1

modM :: Top
modM = TDirective l "module" l "M"

defS :: Top
defS = TDef l "S" [] [Alt l [] Nothing Nothing]

assertFailure :: String -> Text -> Either [Diagnostic] a -> IO ()
assertFailure label needle result = case result of
  Left ds | not (null ds) && any (T.isInfixOf needle . diagMessage) ds ->
    putStrLn (label ++ " " ++ show (length ds))
  Left ds -> die (label ++ ": unexpected diagnostics " ++ show ds)
  Right _ -> die (label ++ ": unexpectedly accepted")

main :: IO ()
main = do
  assertFailure "invariant2_missing_module" "missing %module" (assemble [defS])
  assertFailure "invariant2_duplicate_definition" "duplicate definition of S"
    (assemble [modM, defS, defS])
  assertFailure "invariant2_missing_definition" "type annotation but no definition"
    (assemble [modM, TAnnot l "S" [] [] (Located l "()")])
  assertFailure "invariant2_duplicate_annotation" "duplicate type annotation for S"
    (assemble [modM, TAnnot l "S" [] [] (Located l "()"),
      TAnnot l "S" [] [] (Located l "()"), defS])
  assertFailure "invariant2_invalid_module" "%module expects a module name"
    (assemble [TDirective l "module" l "bad.name", defS])
  assertFailure "invariant2_unknown_directive" "unknown directive %mystery"
    (assemble [modM, TDirective l "mystery" l "x", defS])
  assertFailure "invariant2_duplicate_directive" "duplicate %module directive"
    (assemble [modM, modM, defS])
  assertFailure "invariant2_missing_argument" "%module needs an argument"
    (assemble [TDirective l "module" l "", defS])
  assertFailure "invariant2_unexpected_argument" "%syntax takes no argument"
    (assemble [modM, TDirective l "syntax" l "x", defS])
  assertFailure "invariant2_library" "%library and %module"
    (assemble [TDirective l "library" l "", modM, defS])
  assertFailure "invariant2_invalid_import" "%import expects a path"
    (assemble [modM, TDirective l "import" l "../x.hpeg", defS])
  assertFailure "invariant2_duplicate_import" "is imported twice"
    (assemble [modM, TDirective l "import" l "x.hpeg",
      TDirective l "import" l "x.hpeg", defS])
  assertFailure "invariant2_invalid_recover" "%recover expects a label and a rule name"
    (assemble [modM, TDirective l "recover" l "onlyone", defS])
  assertFailure "invariant2_invalid_language" "%language expects extension names"
    (assemble [modM, TDirective l "language" l "lowercase", defS])
  assertFailure "invariant2_invalid_export" "%export expects export items"
    (assemble [modM, TDirective l "export" l "bad(", defS])
  assertFailure "invariant2_invalid_deriving" "%deriving expects class names"
    (assemble [modM, TDirective l "deriving" l "lowercase", defS])
  assertFailure "invariant2_invalid_string" "the description is empty"
    (assemble [modM, TDirective l "expect" l "S \"\"", defS])
  assertFailure "invariant2_duplicate_string" "duplicate %expect for rule S"
    (assemble [modM, TDirective l "expect" l "S \"x\"",
      TDirective l "expect" l "S \"y\"", defS])
  assertFailure "invariant2_invalid_safe" "%safe expects a label name"
    (assemble [modM, TDirective l "safe" l "bad-name", defS])
  assertFailure "invariant2_invalid_rule_name" "%start expects a rule name"
    (assemble [modM, TDirective l "start" l "bad-name", defS])
  assertFailure "invariant2_invalid_tabstop" "%tabstop expects a positive integer"
    (assemble [modM, TDirective l "tabstop" l "0", defS])
  assertFailure "invariant2_missing_template_type" "has parameters, so it needs a type annotation"
    (assemble [modM, TDef l "S" ["x"] [Alt l [] Nothing Nothing]])
  assertFailure "invariant2_template_mismatch" "template parameters of the definition"
    (assemble [modM, TAnnot l "S" [] [TemplateParam "x" Nothing] (Located l "()"),
      TDef l "S" ["y"] [Alt l [] Nothing Nothing]])
  assertFailure "invariant2_no_rules" "the grammar has no rules" (assemble [modM])
  assertFailure "invariant2_public_missing_module" "missing %module"
    (generateWithWarnings defaultOptions Nothing [] "S <- 'a'\n")
  assertFailure "invariant2_public_duplicate_definition" "duplicate definition of S"
    (generateWithWarnings defaultOptions Nothing [] "%module M\nS <- 'a'\nS <- 'b'\n")
