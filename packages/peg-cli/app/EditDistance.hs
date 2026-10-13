-- | The edit distance, to suggest a command for a misspelt one (ADR 0046).
module EditDistance (editDistance, suggestions) where

import Data.List (foldl')

-- | The Levenshtein distance: the fewest insertions, deletions and
-- substitutions of characters that turn one string into the other.
editDistance :: String -> String -> Int
editDistance a b = last (foldl' step [0 .. length a] b)
  where
    step prev@(p : ps) c = scanl compute (p + 1) (zip3 a prev ps)
      where
        compute left (x, diag, up) = minimum [left + 1, up + 1, diag + fromEnum (x /= c)]
    step [] _ = []

-- | The candidates nearest to a word, if they are at most 2 edits away.
suggestions :: [String] -> String -> [String]
suggestions candidates word =
  case [(editDistance word c, c) | c <- candidates] of
    [] -> []
    scored ->
      let best = minimum (map fst scored)
       in if best <= 2 then [c | (d, c) <- scored, d == best] else []
