-- | Syntax trees produced by the CommonMark grammars (ADR 0011).
module Conformance.CommonMark.Types
  ( -- * Blocks
    Block (..)
  , ListType (..)
  , Container (..)
  , FenceInfo (..)
    -- * Inlines
  , Inline (..)
  , RefMap
    -- * Containers
  , isQuote
  , itemColumn
  , lastContainer
  , dropInnermost
  , normalizeLabel
  ) where

import Data.Map.Strict (Map)
import Data.Text (Text)
import qualified Data.Text as T

-- | Blocks, before inline parsing. Leaf blocks keep their raw inline text.
data Block
  = Paragraph Text
  | Heading Int Text
  | ThematicBreak
  | -- | Info string (raw) and contents.
    CodeBlock (Maybe Text) Text
  | HtmlBlock Text
  | BlockQuote [Block]
  | -- | A list item, merged into lists after parsing.
    Item ListType [Block]
  | List ListType Bool [[Block]]
  | -- | A link reference definition: raw label, destination, title.
    RefDef Text Text (Maybe Text)
  | BlankLine
  deriving (Eq, Show)

data ListType
  = Bullet Char
  | -- | Start number and delimiter.
    Ordered Int Char
  deriving (Eq, Ord, Show)

-- | Open containers, outermost first. Each line inside a container must
-- start with the container's continuation prefix.
data Container
  = Quote
  | -- | A list item whose content starts at the given 0-based column.
    ItemAt Int
  deriving (Eq, Ord, Show)

-- | A code fence: character, length and indentation of the opening fence.
data FenceInfo = FenceInfo Char Int Int
  deriving (Eq, Ord, Show)

isQuote :: [Container] -> Bool
isQuote (Quote : _) = True
isQuote _ = False

-- | The content column of the outermost container if it is a list item.
itemColumn :: [Container] -> Maybe Int
itemColumn (ItemAt w : _) = Just w
itemColumn _ = Nothing

lastContainer :: [Container] -> Maybe Container
lastContainer [] = Nothing
lastContainer cs = Just (last cs)

dropInnermost :: [Container] -> [Container]
dropInnermost [] = []
dropInnermost cs = init cs

-- | Inlines. Delimiter runs are resolved into emphasis after parsing.
data Inline
  = Str Text
  | SoftBreak
  | HardBreak
  | Code Text
  | RawHtml Text
  | Autolink Text Text
  | -- | Link text, destination, title.
    Link [Inline] Text (Maybe Text)
  | Image [Inline] Text (Maybe Text)
  | -- | A run of @*@ or @_@: character, length, and the byte offsets of
    -- the run in the inline text. The characters around the run, which
    -- decide whether it can open or close emphasis, are looked up from
    -- the offsets after parsing.
    Delim Char Int Int Int
  | Emph [Inline]
  | Strong [Inline]
  deriving (Eq, Show)

-- | Link reference definitions by normalized label.
type RefMap = Map Text (Text, Maybe Text)

-- | Case fold and collapse whitespace (CommonMark link label matching).
normalizeLabel :: Text -> Text
normalizeLabel = T.unwords . T.words . T.toCaseFold
