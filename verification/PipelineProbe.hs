{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import Data.Either (isLeft, isRight)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Codegen (Generation (..), Options (..), defaultOptions, generateWithWarnings)
import Peg.Grammar (Diagnostic (..))
import Peg.Grammar.Check (check)
import Peg.Grammar.Import (resolveImports)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import System.Exit (die)

good :: Text
good = "%module M\nS :: ()\nS <- 'a' { () }\n"

checkCase :: String -> String -> Text -> Options -> Maybe Text -> Text -> IO ()
checkCase label expected needle opts strip source = do
  let result = generateWithWarnings opts strip [] source
      observed = case result of
        Left ds -> ("outer", ds)
        Right gen -> case generationModule gen of
          Left ds -> ("inner", ds)
          Right _ -> ("success", [])
      (stage, diags) = observed
  unless (stage == expected &&
          (stage == "success" || not (null diags) && any (T.isInfixOf needle . diagMessage) diags)) $
    die ("invariant2: " ++ label ++ ": expected " ++ expected ++ "/" ++ T.unpack needle ++
         ", got " ++ stage ++ "/" ++ show (map diagMessage diags))
  putStrLn (label ++ " " ++ stage ++ " " ++ show (length diags))

main :: IO ()
main = do
  let importSource = "%module M\n%import missing.hpeg\nS <- 'a'\n"
      expandSource = "%module M\nS <- Missing<'a'>\n"
      checkSource = "%module M\nS <- Absent\n"
      resolved src = parseGrammar src >>= \g -> resolveImports g []
      expanded src = resolved src >>= expandTemplates
      failsAt stage result = isRight result && isLeft (result >>= stage)
  let mixedImports = "%module M\n%import missing.hpeg\n%import module.hpeg\nS <- 'a'\n"
  case parseGrammar mixedImports >>= \g -> resolveImports g [("module.hpeg", good)] of
    Left ds | [missing, notLibrary] <- map diagMessage ds
            , "no such file" `T.isInfixOf` missing
            , "no %library directive" `T.isInfixOf` notLibrary -> pure ()
    other -> die ("invariant2: expected both library errors in import order: " ++ show other)
  unless (failsAt (\g -> resolveImports g []) (parseGrammar importSource)) $
    die "invariant2: import case did not reach and fail import resolution"
  unless (failsAt expandTemplates (resolved expandSource)) $
    die "invariant2: expansion case did not reach and fail template expansion"
  unless (failsAt check (expanded checkSource)) $
    die "invariant2: check case did not reach and fail rule checking"
  checkCase "invariant2_parse" "outer" "" defaultOptions Nothing "%module M\n]"
  checkCase "invariant2_import" "outer" "cannot import" defaultOptions Nothing
    importSource
  checkCase "invariant2_expand" "outer" "template" defaultOptions Nothing
    expandSource
  checkCase "invariant2_check" "outer" "undefined rule" defaultOptions Nothing
    checkSource
  checkCase "invariant2_generate_module" "inner" "generated module name is invalid"
    defaultOptions (Just "invalid") good
  checkCase "invariant2_generate_filename" "inner" "file name contains a control character"
    defaultOptions { optOutputName = "bad\nname.hs" } Nothing good
  checkCase "invariant2_success" "success" "" defaultOptions Nothing good
