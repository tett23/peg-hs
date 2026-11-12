-- Translate the named productions in Happy's info file to the symbol numbers
-- used by its debug parser. Fail if a symbol or production cannot be resolved.
module Main (main) where

import Control.Monad (unless)
import Data.List (intercalate, nub, sortOn, stripPrefix)
import Data.Ord (Down(..))
import qualified Data.Map.Strict as M
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

type Row = (String, [String])

production :: (Int, String) -> Either String Row
production (expected, line) = case words line of
  lhs : "->" : rest | not (null rest), last rest == "(" ++ show expected ++ ")" ->
    Right (lhs, init rest)
  _ -> Left ("unexpected production " ++ show expected ++ ": " ++ line)

-- Kernel reduction of an Array literal traverses its construction. A balanced
-- lookup keeps every concrete rule lookup logarithmic during proof checking.
lookupTree :: Int -> [String] -> String
lookupTree _ [] = "none"
lookupTree _ [row] = "some " ++ row
lookupTree offset rows =
  let half = length rows `div` 2
      pivot = offset + half
      (left, right) = splitAt half rows
   in "(if id < " ++ show pivot ++ " then " ++ lookupTree offset left
        ++ " else " ++ lookupTree pivot right ++ ")"

main :: IO ()
main = do
  args <- getArgs
  (info, parser, table) <- case args of
    [i, p, t] -> (,,) <$> readFile i <*> readFile p <*> pure t
    _ -> die "usage: ExtractHappyGrammar INFO DEBUG-PARSER STACK-TABLE"
  let grammarLines = takeWhile (not . null) (drop 2 (dropWhile (/= "Grammar") (lines info)))
  rows <- either die pure (traverse production (zip [0..] grammarLines))
  names <- case [xs | l <- lines parser, Just raw <- [stripPrefix "happyTokenStrings = " l],
                      Just xs <- [readMaybe raw :: Maybe [String]]] of
    [xs] -> pure xs
    _ -> die "missing or ambiguous Happy terminal table"
  unless (length names == length (nub names)) (die "duplicate terminal")
  let nonterms = M.fromList (zip (nub (map fst rows)) [0 :: Int ..])
      terms = M.fromList (("error", 0) : zip names [2 :: Int ..])
      sym s = case (M.lookup s nonterms, M.lookup s terms) of
        (Just n, Nothing) -> Right (".nonterminal " ++ show n)
        (Nothing, Just n) -> Right (".terminal " ++ show n)
        _ -> Left ("ambiguous or unrecognised symbol: " ++ s)
      spellings = sortOn (Down . length . words) (M.keys nonterms ++ M.keys terms)
      resolve [] = Right []
      resolve input = case [(s, tailWords) | s <- spellings,
                              Just tailWords <- [stripPrefix (words s) input]] of
        (s, tailWords) : _ -> (:) <$> sym s <*> resolve tailWords
        [] -> Left ("unknown production suffix: " ++ unwords input)
      render (lhs, rhs) = do
        symbols <- resolve rhs
        pure ("(" ++ show (nonterms M.! lhs) ++ ", [" ++ intercalate ", " symbols ++ "])")
  unless (take 1 rows == [("%start_parseModuleNoHaddock", ["module"])]) (die "changed start production")
  output <- either die pure (traverse render rows)
  arities <- either die pure (traverse (fmap length . resolve . snd) rows)
  writeFile table (unlines [unwords (map show [i, nonterms M.! lhs, arity])
    | (i, ((lhs, _), arity)) <- zip [0..] (zip rows arities)])
  putStrLn "import HaskellDerivation\nnamespace PegHs.GHCGrammar\nopen CFG"
  putStrLn ("def moduleStart : Nat := " ++ show (nonterms M.! "module"))
  putStrLn ("def productions (id : Nat) : Option Production := if id < " ++ show (length rows)
    ++ " then " ++ lookupTree 0 output ++ " else none\nend PegHs.GHCGrammar")
