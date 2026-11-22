{-# LANGUAGE OverloadedStrings #-}
module InfiniteHeadProbe where

import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T

firstFree :: Integer -> [Integer] -> Integer
firstFree start used = case [k | k <- [start ..], not (k `elem` used)] of
  c : _ -> c
  [] -> -999

-- The same demand and comprehension as Templates.freshName; translation
-- and semantic proofs are also required for Templates itself.
firstName :: Text -> Integer -> S.Set Text -> S.Set Text -> Text
firstName base start used generated = case [c | k <- [start ..], let c = base <> "'" <> T.pack (show (k :: Integer)), not (S.member c used), not (S.member c generated)] of
  c : _ -> c
  [] -> base
