-- Translate the two local counters in directiveComment. The offset counts
-- Unicode characters, as in Text.splitAt; arithmetic is modeled by Nat.
module Main (main) where

import Data.Char (isSpace, ord)
import Data.List (dropWhileEnd)
import System.Environment (getArgs)
import System.Exit (die)

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

branch :: String -> Either String String
branch line = case break (== '>') line of
  (lhs, '>' : rhs) -> do
    (pat, size) <- patternOf (words lhs)
    out <- result size (words rhs)
    pure (pat ++ " => " ++ out)
  _ -> Left line
  where
    patternOf ["[]","-"] = Right ("[]", 0 :: Int)
    patternOf [c,":",tailName,"-"] = do
      x <- char c
      tailPat <- case tailName of
        "rest" -> Right "rest"
        "_" -> Right "_"
        _ -> Left line
      pure (x ++ " :: " ++ tailPat, 1)
    patternOf [c,":","_",":","rest","-"] = do
      x <- char c
      pure (x ++ " :: _ :: rest", 2)
    patternOf _ = Left line
    char "_" = Right "_"
    char raw = case reads raw of
      [(c,"")] | ord c < 128 -> Right (show c)
      _ -> Left line
    result _ ["n"] = Right "n"
    result k [state,"(n","+",delta,"rest"]
      | state `elem` ["outside","inside"], delta == show k ++ ")", k > 0 =
          Right ("translatedOffset " ++ (if state == "inside" then "true" else "false") ++ " (n + " ++ show k ++ ") rest")
    result _ _ = Left line

main :: IO ()
main = do
  [path] <- getArgs
  source <- lines <$> readFile path
  let body = takeWhile (not . null) (dropWhile (/= "    outside n = \\case") source)
  case break (== "    inside n = \\case") body of
    (_ : outer, _ : inner) | not (null outer || null inner) -> do
      let arms q rows = traverse (fmap (("  | " ++ q ++ ", n, ") ++) . branch . trim) rows
      case (++) <$> arms "false" outer <*> arms "true" inner of
        Right rows -> putStr (unlines (["import DirectiveArgument", "namespace PegHs.DirectiveArgument",
          "def translatedOffset : Bool → Nat → List Char → Nat"] ++ rows ++ ["end PegHs.DirectiveArgument"]))
        Left unknown -> die ("unsupported directive comment branch: " ++ unknown)
    _ -> die "missing directiveComment scanner"
