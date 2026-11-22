{-# LANGUAGE OverloadedStrings #-}
module TemplateLibraryProbe where
import Data.Char (isPunctuation, isSymbol, toUpper)
import Data.Maybe (isNothing)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T

numbers :: [Integer]
numbers = [sum ([] :: [Integer]), sum [-3,5], sum [1267650600228229401496703205376], sum [1267650600228229401496703205376, -(1267650600228229401496703205376)]]
flags :: [Bool]
flags = [isNothing missing, isNothing (Just (0 :: Integer)),
  'b' > 'a', 'a' > 'b', isSymbol '+', isSymbol 'a', isPunctuation '(',
  isPunctuation '+', S.null emptyTexts, S.null (S.singleton (T.pack "x"))]
missing :: Maybe Integer
missing = Nothing
emptyTexts :: S.Set Text
emptyTexts = S.empty
texts :: [Text]
texts = [T.singleton (toUpper 'ß'), T.singleton (toUpper 'é'),
  T.cons '空' "", T.cons 'a' "bc", T.filter (/= 'a') "aba",
  T.filter (/= 'a') "", T.singleton (T.head "空x"), T.pack (show (-(1267650600228229401496703205376) :: Integer)),
  "\0\n\r\t\DEL", "𐐨"]
scanned :: [Integer]
scanned = scanl (+) 0 [1,-2,3]
dropped :: [Integer]
dropped = dropWhile (< 3) [1,2,3,1]
ascending :: [Text]
ascending = S.toAscList (S.fromList ["z","a","空","a"])
