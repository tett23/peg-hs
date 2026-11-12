{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Codegen (Generation (..), Options (..), defaultOptions, generateWithWarnings)
import Peg.Grammar (Diagnostic (..))
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
  checkCase "invariant2_parse" "outer" "" defaultOptions Nothing "%module M\n]"
  checkCase "invariant2_import" "outer" "cannot import" defaultOptions Nothing
    "%module M\n%import missing.hpeg\nS <- 'a'\n"
  checkCase "invariant2_expand" "outer" "template" defaultOptions Nothing
    "%module M\nS <- Missing<'a'>\n"
  checkCase "invariant2_check" "outer" "undefined rule" defaultOptions Nothing
    "%module M\nS <- Absent\n"
  checkCase "invariant2_generate_module" "inner" "generated module name is invalid"
    defaultOptions (Just "invalid") good
  checkCase "invariant2_generate_filename" "inner" "file name contains a control character"
    defaultOptions { optOutputName = "bad\nname.hs" } Nothing good
  checkCase "invariant2_success" "success" "" defaultOptions Nothing good
