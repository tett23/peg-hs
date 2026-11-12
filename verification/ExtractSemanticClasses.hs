module Main (main) where

import Data.Char (chr, isAlpha, isAlphaNum, isSpace)
import Data.List (intercalate)

intervals :: (Char -> Bool) -> [(Int, Int)]
intervals predicate = foldr include [] [0 .. 0x10ffff]
  where
    include n rest
      | (n >= 0xd800 && n <= 0xdfff) || not (predicate (chr n)) = rest
      | otherwise = case rest of
          (lo, hi) : more | lo == n + 1 -> (n, hi) : more
          _ -> (n, n) : rest

main :: IO ()
main = do
  putStrLn "import SemanticPredicates\nnamespace PegHs.GhcPredicates\nopen SemanticPredicates"
  mapM_ emit [("space", isSpace), ("alpha", isAlpha), ("alnum", isAlphaNum)]
  putStrLn "def classes : Classes := ⟨space, alpha, alnum⟩"
  putStrLn "theorem invariant1_actual_classes (k : Kind) (e : Env) : eval classes k e = true ↔ Holds classes e k := invariant1_eval_iff .."
  putStrLn "end PegHs.GhcPredicates"
  where
    emit (name, predicate) = do
      let rows = intervals predicate
      putStrLn ("def " ++ name ++ "Ranges : List (Nat × Nat) := [" ++ intercalate ", " (map show rows) ++ "]")
      putStrLn ("def " ++ name ++ " (c : Char) : Bool := " ++ name ++ "Ranges.any fun (lo, hi) => lo ≤ c.toNat && c.toNat ≤ hi")
