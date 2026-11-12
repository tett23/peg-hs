-- Translate the name and occurrence guards used by assemble's directive diagnostics.
module Main (main) where

import Control.Monad (unless)
import Data.Char (isAsciiLower)
import Data.List (stripPrefix, tails)
import System.Environment (getArgs)
import System.Exit (die)

names :: [String] -> String -> String -> IO String
names source prefix suffix = case [rest | line <- source, Just rest <- [stripPrefix prefix line]] of
  [rest] -> case reads rest :: [([String], String)] of
    [(xs, tailText)] | tailText == suffix -> do
      unless (all (\x -> not (null x) && all isAsciiLower x) xs) (die "unsupported directive name")
      pure (show xs)
    _ -> die ("unsupported name list or guard after " ++ prefix)
  _ -> die ("missing or repeated assembler clause " ++ prefix)

main :: IO ()
main = do
  [path] <- getArgs
  source <- lines <$> readFile path
  known <- names source "    known = " ""
  optional <- names source
    "        ++ [Diagnostic l (\"%\" <> n <> \" needs an argument\") | (l, n, a) <- directives, n `elem` known, n `notElem` "
    ", T.null a]"
  flags <- names source
    "        ++ [Diagnostic l (\"%\" <> n <> \" takes no argument\") | (l, n, a) <- directives, n `elem` "
    ", not (T.null a)]"
  let duplicateStart = "        ++ [ Diagnostic l (\"duplicate %\" <> n <> \" directive\")"
      duplicateGuard = "           , (l, _, _) : _ : _ <- [reverse [d | d@(_, n', _) <- directives, n' == n]]"
  unique <- case [clause | first : clause <- tails source, first == duplicateStart] of
    [listLine : guardLine : "           ]" : _] | guardLine == duplicateGuard ->
      names [listLine] "           | n <- " ""
    _ -> die "unsupported duplicate directive clause"
  putStrLn "import DirectiveAssembly"
  putStrLn "namespace PegHs.TranslatedArity"
  putStrLn ("def known : List String := " ++ known)
  putStrLn ("def optional : List String := " ++ optional)
  putStrLn ("def flags : List String := " ++ flags)
  putStrLn ("def uniqueNames : List String := " ++ unique)
  putStrLn "def duplicateLocation (n : String) (ds : List (α × String × String)) : Option α :="
  putStrLn "  match (ds.filter (fun d => d.2.1 == n)).reverse with"
  putStrLn "  | (l, _, _) :: _ :: _ => some l"
  putStrLn "  | _ => none"
  putStrLn "end PegHs.TranslatedArity"
