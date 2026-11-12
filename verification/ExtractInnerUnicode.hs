import Data.Char (chr, isAlphaNum, isUpper)
import Numeric (showHex)

scalarPoints :: [Int]
scalarPoints = [0 .. 0xD7FF] ++ [0xE000 .. 0x10FFFF]

ranges :: (Char -> Bool) -> [(Int, Int)]
ranges predicate = reverse (go Nothing [] scalarPoints)
  where
    go current output [] = maybe output (: output) current
    go current output (point : rest)
      | predicate (chr point) = case current of
          Nothing -> go (Just (point, point)) output rest
          Just (first, lastPoint)
            | point == lastPoint + 1 -> go (Just (first, point)) output rest
            | otherwise -> go (Just (point, point)) ((first, lastPoint) : output) rest
      | otherwise = go Nothing (maybe output (: output) current) rest

hex :: Int -> String
hex value = "0x" ++ showHex value ""

emit :: String -> [(Int, Int)] -> IO ()
emit name spans = do
  putStrLn ("def " ++ name ++ " : List (Nat × Nat) := [")
  mapM_ (\(first, lastPoint) ->
    putStrLn ("  (" ++ hex first ++ ", " ++ hex lastPoint ++ "),")) spans
  putStrLn "]"

main :: IO ()
main = do
  emit "upperRanges" (ranges isUpper)
  emit "alphaNumRanges" (ranges isAlphaNum)
