-- GHC 9.10.3's uppercase mapping, grouped into runs with constant offset.
import Data.Char (chr, ord, toUpper, generalCategory, isSymbol, isPunctuation)
import Numeric (showHex)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  args <- getArgs
  let mappings = [(p, ord (toUpper (chr p))) | p <- [0 .. 0x10ffff], ord (toUpper (chr p)) /= p]
  case args of
    [] -> mapM_ emit (runs mappings)
    ["--pairs"] -> mapM_ (\(p, q) -> putStrLn (show p ++ " " ++ show q)) mappings
    ["--classifications"] -> mapM_ classification
      (0 : concat [[n - 1, n] | n <- [1 .. 0x10ffff], generalCategory (chr (n - 1)) /= generalCategory (chr n)] ++ [0x10ffff])
    _ -> die "usage: ExtractUpperCase [--pairs | --classifications]"
  where
    classification n = putStrLn (unwords [show n, flag (isSymbol (chr n)), flag (isPunctuation (chr n))])
    flag value = if value then "1" else "0"
    emit (a, b, target) = putStrLn ("  (0x" ++ showHex a "" ++ ", 0x" ++ showHex b "" ++ ", 0x" ++ showHex target "" ++ "),")
    runs [] = []
    runs ((a, target) : rest) = extend a a target rest
    extend a b target ((p, q) : rest)
      | p == b + 1 && q == target + p - a = extend a p target rest
    extend a b target rest = (a, b, target) : runs rest
