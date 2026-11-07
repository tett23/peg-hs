module Main (main) where

import Calc.Greeting (greeting)
import Calc.Parser (parse)
import qualified Data.Text.IO as TIO
import Peg.Runtime (renderParseError)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  hPutStrLn stderr greeting
  input <- TIO.getLine
  case parse input of
    Right expr -> print expr
    Left err -> TIO.putStrLn (renderParseError err)
