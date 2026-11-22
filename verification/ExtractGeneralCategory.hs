-- Print the runs of Data.Char.generalCategory over the code points as the
-- Lean table HsPrelude.generalCategoryRanges: (first, last, the index of the
-- category in the order of GeneralCategory's constructors). The runs of
-- ModifierLetter are left out (they are AssembleChars.modifierRanges), and so
-- are the runs of NotAssigned (the default). check-translate-assemble.sh
-- diffs the output against HsPrelude.lean.
import Data.Char (GeneralCategory (..), chr, generalCategory)
import Numeric (showHex)

main :: IO ()
main = mapM_ line (runs [(p, generalCategory (chr p)) | p <- [0 .. 0x10FFFF]])
  where
    line (a, b, c)
      | c `elem` [ModifierLetter, NotAssigned] = pure ()
      | otherwise = putStrLn ("  (0x" ++ showHex a "" ++ ", 0x" ++ showHex b "" ++ ", " ++ show (fromEnum c) ++ "),")
    runs ((p, c) : rest) = go p p c rest
    runs [] = []
    go a _ c ((q, d) : rest) | d == c = go a q c rest
    go a b c rest = (a, b, c) : runs rest
