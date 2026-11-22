{-# LANGUAGE OverloadedStrings #-}
module TemplateCollectionsProbe where
import Data.List (nub)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)

unionValues :: [(Text, Integer)] -> [(Text, Integer)] -> [(Text, Integer)]
unionValues left right = M.toList (M.union (M.fromList left) (M.fromList right))
mappedValues :: [(Text, Integer)] -> [(Text, Integer)]
mappedValues pairs = M.toList (M.map (+ 10) (M.fromList pairs))
intersectionValues :: [Text] -> [Text] -> [Text]
intersectionValues left right = S.toList (S.intersection (S.fromList left) (S.fromList right))
deduplicated :: [Text] -> [Text]
deduplicated = nub

emptyMap :: M.Map Text Integer
emptyMap = M.empty
mapA, mapB :: M.Map Text Integer
mapA = M.fromList [("b",2),("a",1)]
mapB = M.fromList [("a",1),("b",2)]
setA, setB :: S.Set Text
setA = S.fromList ["b","a"]
setB = S.fromList ["a","b"]
flags :: [Bool]
flags = [M.null emptyMap, M.null mapA, show mapA == show mapB, show setA == show setB]
