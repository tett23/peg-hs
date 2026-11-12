{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (forM_)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Peg.Grammar.Highlight (highlights)
import Peg.Grammar.Parser (parseTops)
import System.Environment (getArgs)
import System.FilePath ((</>))

cases :: [Text]
cases =
  ["", "%module M\n", "Start <- ]\n", "S <- [z-a]", "S <- [a-z]",
   "S <- '\\u{110000}'", "S <- '\\u{10FFFF}'", "S <- 'unterminated",
   "S <- &{ True }", "S <- !{ False }", "S <- ('λ' / 'β') ^msg",
   "λ <- 'α'", "%module M\r\nS <- .\r\n", "S ::   \nS <- .",
   "T<p> <- p\nS <- T<('a' / 'b')>", "S <- Missing"]
  ++ [ "Start <- " <> expression <> "\n"
     | n <- [254, 255, 256, 257],
       expression <- [T.replicate n "&" <> "'x'",
                      "'x'" <> T.replicate n "?",
                      "('x'" <> T.replicate n "?" <> ") ^lab",
                      "('x' / 'y'" <> T.replicate n "*" <> ")?"] ]

main :: IO ()
main = do
  [directory] <- getArgs
  forM_ (zip [0 :: Int ..] cases) $ \(i, source) -> do
    let file = directory </> show i
    T.writeFile file source
    strict <- case parseTops source of
      Right _ -> pure "ok"
      Left [_] -> pure "error"
      Left ds -> fail ("expected one parse diagnostic, got " ++ show (length ds) ++ " for " ++ file)
    let syntax = maybe "error" (const "ok") (highlights source)
    putStrLn (unwords [strict, syntax, file])
