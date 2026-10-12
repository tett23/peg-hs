{-# LANGUAGE OverloadedStrings #-}

-- | The ranges of the tokens of the grammars of the repository, which the
-- tests of the editor grammars compare with theirs (ADR 0034).
module Ranges (rangeTests) where

import qualified Data.ByteString.Lazy as BL
import Data.List (isPrefixOf, sortOn)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Grammar (Loc (..))
import Peg.Grammar.Highlight
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)

-- | Compared with the editor grammars: the kinds whose ranges the three
-- grammars agree on.
compared :: [(HighlightKind, Text)]
compared =
  [ (HComment, "comment")
  , (HLiteral, "literal")
  , (HClass, "class")
  , (HAction, "action")
  , (HRuleName, "rule-name")
  , (HLabel, "label")
  ]

rangeTests :: [FilePath] -> TestTree
rangeTests files =
  goldenVsString "the ranges for the editor grammars (ADR 0034)" "../../editors/test/ranges.txt" $ do
    let named = sortOn fst [(repoPath f, f) | f <- files]
    blocks <- mapM (\(name, f) -> block name <$> TIO.readFile f) named
    pure (BL.fromStrict (TE.encodeUtf8 (T.concat blocks)))
  where
    block name src =
      T.unlines $
        ("== " <> T.pack name)
          : [ k <> " " <> pos (hlStart h) <> "-" <> pos (hlEnd h)
            | h <- maybe [] id (highlights src)
            , Just k <- [lookup (hlKind h) compared]
            ]
    pos (Loc l c) = T.pack (show l) <> ":" <> T.pack (show c)

-- A path relative to the package as a path relative to the repository.
repoPath :: FilePath -> FilePath
repoPath f
  | "../../" `isPrefixOf` f = drop 6 f
  | "../" `isPrefixOf` f = "packages/" <> drop 3 f
  | otherwise = "packages/peg-grammar/" <> f
