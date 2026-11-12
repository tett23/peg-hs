-- Recognition projection of the generated strict File rule. Child calls, memo
-- hits, and runtime combinators retain their separate semantic obligations.
module Main (main) where

import Control.Monad (forM_, guard)
import Data.Char (isDigit, isSpace, ord)
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

-- Call sites are numbered by occurrence; targets are resolved against the
-- rule names accepted here. The independent metagrammar extraction checks IDs.
call :: Int -> ReadP String
call site = do
  token "peg'rule'"
  target <- choice [string name >> pure number | (name, number) <-
    [("TopItem","1"), ("TopOne","2"), ("Ws","4"), ("SpaceChar","5"),
     ("Comment","6"), ("IdentStart","9"), ("IdentChar","10"), ("Verbatim","11"), ("Directive","12"), ("Declaration","13")]]
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
  pure (".seq " ++ ws ++ " (.seq (.star " ++ item ++ ") (.label " ++
    leanString label ++ " (some " ++ leanString message ++ ") (.notAhead (.terminal 0))))")

header :: String -> ReadP ()
header name = mapM_ token ["peg'rule'" ++ name, "=", "PegRt.memo", "peg'memo'" ++ name,
  show name, "(", "PegRt.choice", "["]

topItem :: ReadP String
topItem = do
  header "TopItem"
  mapM_ token ["do", "{", "peg'v0", "<-"]
  item <- call 2
  mapM_ token [";", "_", "<-"]
  ws <- call 3
  mapM_ token [";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  pure (".seq " ++ item ++ " " ++ ws)

topOne :: ReadP String
topOne = do
  header "TopOne"
  let branch site binder = do
        mapM_ token ["do", "{", binder, "<-"]
        value <- call site
        mapM_ token [";", "PegPrelude.pure", binder, "}"]
        pure value
  first <- branch 4 "peg'v0"
  token ","
  second <- branch 5 "peg'v1"
  token ","
  third <- branch 6 "peg'v2"
  mapM_ token ["]", ")"]
  pure (".alt " ++ first ++ " (.alt " ++ second ++ " " ++ third ++ ")")

whitespace :: ReadP String
whitespace = do
  header "Ws"
  mapM_ token ["do", "{", "_", "<-", "PegRt.skipMany", "(", "PegRt.choice", "["]
  let ignored site = do
        mapM_ token ["do", "{", "_", "<-"]
        value <- call site
        mapM_ token [";", "PegPrelude.pure", "()", "}"]
        pure value
  space <- ignored 7
  token ","
  comment <- ignored 8
  mapM_ token ["]", ")", ";", "PegPrelude.pure", "()", "}", "]", ")"]
  pure (".star (.alt " ++ space ++ " " ++ comment ++ ")")

-- Only the generated LINE and COLUMN pragmas may surround embedded expressions.
pragma :: String -> ReadP ()
pragma name = do
  mapM_ token ["{-#", name]
  skipSpaces
  _ <- munch1 isDigit
  if name == "LINE" then quoted >> pure () else pure ()
  token "#-}"

embedded :: [String] -> ReadP ()
embedded expr = pragma "LINE" >> pragma "COLUMN" >> mapM_ token expr >> pragma "LINE"

filteredChar :: String -> String -> Int -> Int -> ReadP String
filteredChar name predicate site terminal = do
  header name
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "c", "<-",
    "PegRt.capture", "(", "PegRt.anyChar", ")", ";", "PegRt.predicate", "(", "\\_col", "->"]
  embedded [predicate, "(", "firstChar", "c", ")"]
  mapM_ token [")", ";", "_span", "<-", "PegRt.spanFrom", "peg'start", ";", "PegPrelude.pure", "("]
  embedded ["()"]
  mapM_ token [")", "}", "]", ")"]
  pure (".seq (.bind " ++ show site ++ " \"c\" (.capture (.terminal " ++ show terminal ++
    "))) (.predicate " ++ show site ++ ")")

identifier :: ReadP String
identifier = do
  header "Ident"
  mapM_ token ["do", "{", "peg'v0", "<-", "PegRt.capture", "(", "PegRt.choice", "[",
    "do", "{", "_", "<-"]
  initial <- call 9
  mapM_ token [";", "_", "<-", "PegRt.skipMany", "("]
  following <- call 10
  mapM_ token [")", ";", "PegPrelude.pure", "()", "}", "]", ")", ";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  pure (".capture (.seq " ++ initial ++ " (.star " ++ following ++ "))")

commentRule :: ReadP String
commentRule = do
  header "Comment"
  let literal c = do
        token "PegRt.lit"
        value <- quoted
        guard (value == [c])
        _ <- quoted -- expected-token text does not affect recognition
        pure ()
  mapM_ token ["do", "{"]
  literal '#'
  mapM_ token [";", "PegRt.skipMany", "(", "PegRt.choice", "[", "do", "{", "PegRt.notP", "("]
  literal '\n'
  mapM_ token [")", ";", "PegRt.anyChar", ";", "PegPrelude.pure", "()", "}", "]", ")",
    ";", "PegPrelude.pure", "()", "}", "]", ")"]
  pure ".seq (.terminal 2) (.star (.seq (.notAhead (.terminal 3)) (.terminal 4)))"

main :: IO ()
main = do
  [path] <- getArgs
  source <- lines <$> readFile path
  putStrLn "import MetaExecution\nnamespace PegHs.MetaExecution"
  forM_ [("File", production), ("TopItem", topItem), ("TopOne", topOne), ("Ws", whitespace),
         ("SpaceChar", filteredChar "SpaceChar" "isSpace" 0 1), ("Comment", commentRule), ("Ident", identifier),
         ("IdentStart", filteredChar "IdentStart" "isIdentStart" 1 6),
         ("IdentChar", filteredChar "IdentChar" "isIdentChar" 2 7)] $
    \(name, parser) -> case [unlines (l : takeWhile (not . all isSpace) rest) |
        l : rest <- tails source, l == "peg'rule'" ++ name ++ " ="] of
      [body] | [(expr, "")] <- readP_to_S (parser <* skipSpaces <* eof) body ->
        putStrLn ("def translatedStrict" ++ name ++ " : EnvironmentEval.Body := " ++ expr)
      _ -> die ("unsupported or missing generated rule " ++ name)
  putStrLn "end PegHs.MetaExecution"
