-- Recognition projection of the generated strict File rule. Child calls, memo
-- hits, and runtime combinators retain their separate semantic obligations.
module Main (main) where

import Data.Char (isSpace, ord)
import Data.List (intercalate, tails)
import System.Environment (getArgs)
import System.Exit (die)
import Text.ParserCombinators.ReadP

token :: String -> ReadP ()
token s = skipSpaces >> string s >> pure ()

quoted :: ReadP String
quoted = skipSpaces >> readS_to_P reads

leanString :: String -> String
leanString s = "(String.ofList [" ++ intercalate ", " ["Char.ofNat " ++ show (ord c) | c <- s] ++ "])"

-- Call sites are numbered by occurrence; targets are resolved against the two
-- rule names accepted here. The independent metagrammar extraction checks IDs.
call :: Int -> ReadP String
call site = do
  token "peg'rule'"
  target <- (string "Ws" >> pure "4") +++ (string "TopItem" >> pure "1")
  pure ("(.call " ++ show site ++ " " ++ target ++ ")")

production :: ReadP String
production = do
  mapM_ token ["peg'rule'File", "=", "PegRt.memo", "peg'memo'File", "\"File\"",
    "(", "PegRt.choice", "[", "do", "{", "_", "<-"]
  ws <- call 0
  mapM_ token [";", "peg'v0", "<-", "PegRt.many", "("]
  item <- call 1
  mapM_ token [")", ";", "PegRt.labeledMessage"]
  label <- quoted
  message <- quoted
  mapM_ token ["PegPrelude.Nothing", "(", "PegRt.choice", "[", "do", "{",
    "PegRt.notP", "(", "PegRt.anyChar", ")", ";", "PegPrelude.pure", "(", ")",
    "}", "]", ")", ";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  skipSpaces >> eof
  pure (".seq " ++ ws ++ " (.seq (.star " ++ item ++ ") (.label " ++
    leanString label ++ " (some " ++ leanString message ++ ") (.notAhead (.terminal 0))))")

main :: IO ()
main = do
  [path] <- getArgs
  source <- lines <$> readFile path
  case [unlines (l : takeWhile (not . all isSpace) rest) |
        l : rest <- tails source, l == "peg'rule'File ="] of
    [body] | [(expr, "")] <- readP_to_S production body ->
      putStrLn ("import MetaExecution\nnamespace PegHs.MetaExecution\n" ++
        "def translatedStrictFile : EnvironmentEval.Body := " ++ expr ++
        "\nend PegHs.MetaExecution")
    _ -> die "unsupported or missing generated File rule"
