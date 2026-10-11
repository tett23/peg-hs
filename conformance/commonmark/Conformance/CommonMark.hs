-- | CommonMark to HTML with the generated grammars (ADR 0011).
--
-- All input is matched by the generated parsers. The steps here are pure
-- transformations of the parsed trees: merging list items into lists,
-- collecting link reference definitions, resolving emphasis and rendering.
module Conformance.CommonMark
  ( toHtml
  , toHtmlV1
  ) where

import qualified Conformance.CommonMark.Block as Block
import qualified Conformance.CommonMark.V1.Block as V1Block
import qualified Conformance.CommonMark.V1.Inline as V1Inline
import Conformance.CommonMark.Emphasis (resolveEmphasis)
import Conformance.CommonMark.Entities (entities)
import Conformance.CommonMark.Inline (InlineEnv (..))
import qualified Conformance.CommonMark.Inline as Inline
import Conformance.CommonMark.Types
import qualified Data.ByteString as B
import Data.Char (chr, digitToInt, isAlphaNum, isAscii, isDigit, isHexDigit, isPunctuation, isSpace, isSymbol)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Peg.Runtime (ParseError, renderParseError)
import Text.Printf (printf)

-- | Parsers for blocks and for the inlines of a leaf block.
data Grammars = Grammars
  { parseBlocks :: Text -> Either ParseError [Block]
  , parseInlines :: RefMap -> Text -> Either ParseError [Inline]
  }

-- | Convert a document. A failure means a grammar did not accept its input.
toHtml :: Text -> Either Text Text
toHtml = convert (Grammars Block.parse (\refs t -> Inline.parse (InlineEnv refs t) t))

-- | Convert with the grammars written without the ADR 0012 extensions,
-- for the first snapshot of ADR 0011.
toHtmlV1 :: Text -> Either Text Text
toHtmlV1 = convert (Grammars V1Block.parse (const V1Inline.parse))

convert :: Grammars -> Text -> Either Text Text
convert g src = do
  blocks <- either (Left . renderParseError) Right (parseBlocks g src)
  let assembled = assemble blocks
      refs = collectRefs assembled
  body <- renderBlocks g refs False (dropRefs assembled)
  pure (finishOutput body)

-- Lists ------------------------------------------------------------------------

sameType :: ListType -> ListType -> Bool
sameType (Bullet a) (Bullet b) = a == b
sameType (Ordered _ a) (Ordered _ b) = a == b
sameType _ _ = False

-- Merge consecutive items of the same type into lists, decide whether each
-- list is loose, and drop blank line markers. Looseness is decided on the
-- raw item contents, which still have their blank line markers.
assemble :: [Block] -> [Block]
assemble blocks = case blocks of
  [] -> []
  Item t bs : rest ->
    let (items, seps, rest') = collect t rest
        raw = bs : items
        loose =
          or (zipWith (\i sep -> sep || endsWithBlank i) raw seps)
            || any internalBlank raw
     in List t (not loose) (map assemble raw) : assemble rest'
  BlankLine : rest -> assemble rest
  BlockQuote bs : rest -> BlockQuote (assemble bs) : assemble rest
  b : rest -> b : assemble rest
  where
    -- Further items of the same type, and whether blank lines separate each
    -- item from the next.
    collect t rest =
      let (blanks, after) = span (== BlankLine) rest
       in case after of
            Item t' bs : more
              | sameType t t' ->
                  let (items, seps, rest') = collect t more
                   in (bs : items, not (null blanks) : seps, rest')
            _ -> ([], [], rest)

-- Whether raw block contents end with a blank line, looking into the last
-- list item as the reference implementations do.
endsWithBlank :: [Block] -> Bool
endsWithBlank bs = case reverse bs of
  BlankLine : _ -> True
  Item _ inner : _ -> endsWithBlank inner
  _ -> False

-- Whether two blocks directly inside an item are separated by a blank line.
internalBlank :: [Block] -> Bool
internalBlank bs = go (dropWhile (== BlankLine) bs)
  where
    go (x : rest) =
      let (blanks, after) = span (== BlankLine) rest
       in case after of
            [] -> False
            y : _
              | not (null blanks) -> True
              | isItem x && not (isItem y) && endsWithBlank [x] -> True
              | otherwise -> go after
    go [] = False
    isItem (Item _ _) = True
    isItem _ = False

-- Reference definitions ------------------------------------------------------------

collectRefs :: [Block] -> RefMap
collectRefs = foldl add M.empty . concatMap defs
  where
    add m (l, d, t) = M.insertWith (\_ old -> old) (normalizeLabel l) (d, t) m
    defs b = case b of
      RefDef l d t -> [(l, d, t)]
      BlockQuote bs -> concatMap defs bs
      List _ _ items -> concatMap (concatMap defs) items
      _ -> []

dropRefs :: [Block] -> [Block]
dropRefs = concatMap drop1
  where
    drop1 b = case b of
      RefDef {} -> []
      BlockQuote bs -> [BlockQuote (dropRefs bs)]
      List t tight items -> [List t tight (map dropRefs items)]
      _ -> [b]

-- Rendering --------------------------------------------------------------------

-- Output pieces. 'Cr' is a newline unless the output already ends in one,
-- as in the reference implementations that produced the spec examples.
data Piece = Lit Text | Cr

finishOutput :: [Piece] -> Text
finishOutput = T.concat . reverse . snd . foldl step (True, [])
  where
    step (atNl, acc) piece = case piece of
      Cr | atNl -> (atNl, acc)
      Cr -> (True, T.pack "\n" : acc)
      Lit t
        | T.null t -> (atNl, acc)
        | otherwise -> (T.takeEnd 1 t == T.pack "\n", t : acc)

renderBlocks :: Grammars -> RefMap -> Bool -> [Block] -> Either Text [Piece]
renderBlocks g refs tight = fmap concat . mapM (renderBlock g refs tight)

renderBlock :: Grammars -> RefMap -> Bool -> Block -> Either Text [Piece]
renderBlock g refs tight b = case b of
  Paragraph t
    | tight -> inlines t
    | otherwise -> do
        is <- inlines t
        pure ([Cr, lit "<p>"] ++ is ++ [lit "</p>", Cr])
  Heading n t -> do
    is <- inlines t
    pure ([Cr, lit ("<h" <> show n <> ">")] ++ is ++ [lit ("</h" <> show n <> ">"), Cr])
  ThematicBreak -> pure [Cr, lit "<hr />", Cr]
  CodeBlock info content ->
    let lang = case fmap (T.takeWhile (not . isSpace) . unescape) info of
          Just l | not (T.null l) -> T.pack " class=\"language-" <> escapeHtml l <> T.pack "\""
          _ -> T.empty
     in pure [Cr, Lit (T.pack "<pre><code" <> lang <> T.pack ">" <> escapeHtml content <> T.pack "</code></pre>"), Cr]
  HtmlBlock t -> pure [Cr, Lit t, Cr]
  BlockQuote bs -> do
    inner <- renderBlocks g refs False bs
    pure ([Cr, lit "<blockquote>", Cr] ++ inner ++ [Cr, lit "</blockquote>", Cr])
  List t isTight items -> do
    rendered <- mapM (renderItem isTight) items
    let (open, close) = case t of
          Bullet _ -> ("<ul>", "</ul>")
          Ordered 1 _ -> ("<ol>", "</ol>")
          Ordered n _ -> ("<ol start=\"" <> show n <> "\">", "</ol>")
    pure ([Cr, lit open, Cr] ++ concat rendered ++ [lit close, Cr])
  Item _ bs -> renderBlocks g refs tight bs
  RefDef {} -> pure []
  BlankLine -> pure []
  where
    lit = Lit . T.pack
    inlines t = do
      is <- either (Left . renderParseError) Right (parseInlines g refs t)
      pure [Lit (renderInlines (resolveEmphasis t is))]
    renderItem isTight bs = do
      inner <- renderBlocks g refs isTight bs
      pure ([lit "<li>"] ++ inner ++ [lit "</li>", Cr])

renderInlines :: [Inline] -> Text
renderInlines = T.concat . map renderInline

renderInline :: Inline -> Text
renderInline i = case i of
  Str t -> escapeHtml t
  SoftBreak -> T.pack "\n"
  HardBreak -> T.pack "<br />\n"
  Code t -> T.pack "<code>" <> escapeHtml t <> T.pack "</code>"
  RawHtml t -> t
  Autolink url txt -> T.pack "<a href=\"" <> escapeHtml (normalizeUrl url) <> T.pack "\">" <> escapeHtml txt <> T.pack "</a>"
  Link xs d t -> T.pack "<a href=\"" <> href d <> T.pack "\"" <> title t <> T.pack ">" <> renderInlines xs <> T.pack "</a>"
  Image xs d t -> T.pack "<img src=\"" <> href d <> T.pack "\" alt=\"" <> escapeHtml (plain xs) <> T.pack "\"" <> title t <> T.pack " />"
  Delim c n _ _ -> T.replicate n (T.singleton c)
  Emph xs -> T.pack "<em>" <> renderInlines xs <> T.pack "</em>"
  Strong xs -> T.pack "<strong>" <> renderInlines xs <> T.pack "</strong>"
  where
    href d = escapeHtml (normalizeUrl (unescape d))
    title = maybe T.empty (\t -> T.pack " title=\"" <> escapeHtml (unescape t) <> T.pack "\"")

-- The plain text of inlines, for the alt attribute of images.
plain :: [Inline] -> Text
plain = T.concat . map one
  where
    one i = case i of
      Str t -> t
      Code t -> t
      SoftBreak -> T.pack "\n"
      HardBreak -> T.pack "\n"
      Link xs _ _ -> plain xs
      Image xs _ _ -> plain xs
      Emph xs -> plain xs
      Strong xs -> plain xs
      Autolink _ t -> t
      RawHtml t -> t
      Delim c n _ _ -> T.replicate n (T.singleton c)

escapeHtml :: Text -> Text
escapeHtml = T.concatMap esc
  where
    esc c = case c of
      '&' -> T.pack "&amp;"
      '<' -> T.pack "&lt;"
      '>' -> T.pack "&gt;"
      '"' -> T.pack "&quot;"
      '\0' -> T.singleton '\xFFFD'
      _ -> T.singleton c

-- Backslash escapes and entity references in destinations, titles and
-- info strings.
unescape :: Text -> Text
unescape = T.pack . go . T.unpack
  where
    go s = case s of
      '\\' : c : rest | isAscii c && (isPunctuation c || isSymbol c) -> c : go rest
      '&' : '#' : x : rest
        | x `elem` ['x', 'X']
        , (h, ';' : rest') <- span isHexDigit rest
        , not (null h)
        , length h <= 6 ->
            T.unpack (codePoint (foldl (\n d -> n * 16 + digitToInt d) 0 h)) ++ go rest'
      '&' : '#' : rest
        | (ds, ';' : rest') <- span isDigit rest
        , not (null ds)
        , length ds <= 7 ->
            T.unpack (codePoint (read ds)) ++ go rest'
      '&' : rest
        | (name, ';' : rest') <- span isAlphaNum rest
        , Just v <- M.lookup (T.pack name) entities ->
            T.unpack v ++ go rest'
      c : rest -> c : go rest
      [] -> []
    codePoint n
      | n == 0 || n > 0x10FFFF || (n >= 0xD800 && n <= 0xDFFF) = T.singleton '\xFFFD'
      | otherwise = T.singleton (chr n)

-- Percent-encode characters that are not safe in a URL, keeping existing
-- escapes, as the reference implementations do.
normalizeUrl :: Text -> Text
normalizeUrl = T.concatMap enc
  where
    safe c = isAscii c && (isAlphaNum c || c `elem` ("-_.!~*'();/?:@&=+$,%#" :: String))
    enc c
      | safe c = T.singleton c
      | otherwise = T.pack (concatMap (printf "%%%02X") (B.unpack (TE.encodeUtf8 (T.singleton c))))
