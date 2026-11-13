module Main (main) where

import Control.Monad (forM_, unless)
import Data.Char (GeneralCategory (..), generalCategory, isAlpha, isAlphaNum, isUpper, ord)
import Data.Word (Word8)
import System.Exit (die)

-- The check script appends adjustChar from the pinned GHC Lexer.x.
main :: IO ()
main = forM_ [minBound .. maxBound] $ \c -> do
  let byte = adjustChar c
      large = byte == 1 || (65 <= byte && byte <= 90)
      small = byte == 2 || (97 <= byte && byte <= 122) || byte == 95
      digit = byte == 3 || (48 <= byte && byte <= 57)
      idchar = large || small || digit || byte == 7 || byte == 39
      exportStart = (isAlpha c || c == '_') && generalCategory c /= ModifierLetter
  unless (c `notElem` " )]\n" || not idchar) $
    die ("generated type delimiter is an identifier character: " ++ show (ord c))
  unless (exportStart == (large || small)) $
    die ("export initial character disagrees with GHC: " ++ show (ord c))
  unless (not (isUpper c) || large) $
    die ("invalid initial module character: " ++ show (ord c))
  unless (not (isAlphaNum c || c == '_' || c == '\'') || idchar) $
    die ("invalid trailing module character: " ++ show (ord c))
