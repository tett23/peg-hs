-- | Tests of the peg-hs executable: warnings, --Werror and --strip-labels
-- (ADR 0028).
module Main (main) where

import Data.List (isInfixOf)
import Control.Monad (when)
import System.Directory (createDirectoryIfMissing, doesFileExist, getTemporaryDirectory, removeFile)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)
import Test.Tasty
import Test.Tasty.HUnit

unsafe :: String
unsafe = "%module M\nS :: ()\nS <- 'a' ('b' ^l) { () } / 'a' 'c' { () }\n"

-- Run peg-hs on a grammar written to a fresh file.
runOn :: String -> String -> [String] -> IO (ExitCode, String, Bool)
runOn name grammar flags = do
  tmp <- getTemporaryDirectory
  let dir = tmp </> "peg-cli-test"
      input = dir </> (name <> ".peg")
      output = dir </> (name <> ".hs")
  createDirectoryIfMissing True dir
  doesFileExist output >>= \e -> when e (removeFile output)
  writeFile input grammar
  (code, _, err) <- readProcessWithExitCode "peg-hs" ([input, "-o", output] ++ flags) ""
  written <- doesFileExist output
  pure (code, err, written)

main :: IO ()
main =
  defaultMain $
    testGroup
      "peg-hs"
      [ testCase "an unsafe label is a warning" $ do
          (code, err, written) <- runOn "warn" unsafe []
          code @?= ExitSuccess
          assertBool err ("3:11: warning: the label l may reject valid input" `isInfixOf` err)
          assertBool "the module is written" written
      , testCase "--Werror fails on a warning" $ do
          (code, err, written) <- runOn "werror" unsafe ["--Werror"]
          code @?= ExitFailure 1
          assertBool err ("warning:" `isInfixOf` err)
          assertBool "no module is written" (not written)
      , testCase "%safe silences the warning" $ do
          (code, err, _) <- runOn "safe" (unsafe <> "%safe l\n") ["--Werror"]
          code @?= ExitSuccess
          err @?= ""
      , testCase "--strip-labels writes the grammar without labels as another module" $ do
          tmp <- getTemporaryDirectory
          (code, _, _) <- runOn "strip" unsafe ["--strip-labels", "N", "--Werror"]
          code @?= ExitSuccess
          out <- readFile (tmp </> "peg-cli-test" </> "strip.hs")
          assertBool "module N" ("module N" `isInfixOf` out)
          assertBool "no label" (not ("labeled" `isInfixOf` out))
      ]
