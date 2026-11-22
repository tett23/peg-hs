{-# LANGUAGE OverloadedStrings #-}
module TemplateMapProbe where
import qualified Data.Map.Strict as M
import Data.Text (Text)

inserted :: Text -> Integer -> [(Text, Integer)] -> Integer
inserted key value pairs = M.findWithDefault (-1) key (M.insert key value (M.fromList pairs))

other :: Text -> Text -> Integer -> [(Text, Integer)] -> Integer
other sought key value pairs = M.findWithDefault (-1) sought (M.insert key value (M.fromList pairs))
