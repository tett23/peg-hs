{-# LANGUAGE OverloadedStrings #-}

-- | Parsing a grammar by its top-level items, reusing the results of the
-- items that did not change since the previous version (ADR 0071). The
-- language server (@Peg.Lsp.Server@ in @peg-lsp@) parses each version of
-- a document this way.
--
-- 'splitFragments' cuts a text into fragments: a fragment starts at the
-- start of the text and after each newline followed by a character that is
-- not a space, a tab, a carriage return, a newline, @/@ or @#@, the rule
-- by which recovery skips to the next top-level item. The inside of a
-- verbatim block (@%{ ... }%@) is not cut.
--
-- 'parseFragments' parses the fragments that are not in the table of the
-- previous version, and returns the table for the next one with the
-- fragments of this version only. The results are those of parsing the
-- whole text at once: 'parsedTops' is 'Peg.Grammar.Parser.parseTops',
-- 'parsedSyntax' the tree and errors of the recovering parse, and
-- 'parsedOutline' 'Peg.Grammar.Outline.outline'. When a fragment has a
-- syntax error, the typed items come from a parse of the whole text, so
-- that the error is the same; the recovering parse joins a fragment with
-- the next one when their boundary could be read differently in the whole
-- text.
--
-- @
-- let p1 = parseFragments noFragments src
--     p2 = parseFragments (parsedFragments p1) edited  -- parses the changed items only
-- in parsedTops p2 == parseTops edited
-- @
module Peg.Grammar.Incremental
  ( splitFragments
  , Fragments
  , noFragments
  , fragmentTexts
  , Parsed (..)
  , parseFragments
  , parseSyntaxWhole
  , syntaxKindName
  ) where

import Data.Char (isSpace)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Unsafe as TU
import Peg.Grammar
import Peg.Grammar.Assemble (Top (..))
import Peg.Grammar.Outline (Outline, OutlinePart, joinOutline, outlineFromTree, outlinePart, shiftOutlinePart)
import Peg.Grammar.Parser (parseTops)
import qualified Peg.Grammar.SelfHosted as SelfHosted
import qualified Peg.Grammar.SelfHostedSyntax as S
import Peg.Runtime (Pos (..), SyntaxError (..))
import Peg.Runtime.Syntax

-- Splitting ----------------------------------------------------------------------

-- | The top-level fragments of a text, in order. Their concatenation is the
-- text; the empty text has none.
splitFragments :: Text -> [Text]
splitFragments t
  | T.null t = []
  | otherwise =
      let n = fragmentLength t
       in TU.takeWord8 n t : splitFragments (TU.dropWord8 n t)

-- The length in bytes of the fragment at the start of a text.
fragmentLength :: Text -> Int
fragmentLength t = skip + scan (TU.dropWord8 skip t)
  where
    -- A verbatim block runs to its first }%, or to the end.
    skip
      | "%{" `T.isPrefixOf` t =
          let (body, rest) = T.breakOn "}%" (T.drop 2 t)
           in if T.null rest then TU.lengthWord8 t else 4 + TU.lengthWord8 body
      | otherwise = 0
    scan s = case T.break (== '\n') s of
      (line, rest) -> case T.uncons (T.drop 1 rest) of
        Nothing -> TU.lengthWord8 s
        Just (c, _)
          | starts c -> TU.lengthWord8 line + 1
          | otherwise -> TU.lengthWord8 line + 1 + scan (T.drop 1 rest)
    starts c = c `notElem` (" \t\r\n/#" :: String)

-- The table --------------------------------------------------------------------------

-- | The results of the fragments of one version, by their text.
newtype Fragments = Fragments (M.Map Text Entry)

-- The results of a fragment, computed when used, with locations relative
-- to the start of the fragment.
data Entry = Entry
  { entryLines :: !Int
  -- ^ The newlines of the fragment.
  , entryBytes :: !Int
  , entryTops :: Maybe [Top]
  -- ^ The typed items, or 'Nothing' for a syntax error.
  , entrySyntax :: (SyntaxNode, [SyntaxError])
  -- ^ The recovering parse.
  , entryOutline :: OutlinePart
  -- ^ The outline of the tree of the recovering parse.
  }

-- | The empty table, for the first version of a document.
noFragments :: Fragments
noFragments = Fragments M.empty

-- | The texts of the fragments in a table, in the order of 'Text'. For
-- tests.
fragmentTexts :: Fragments -> [Text]
fragmentTexts (Fragments m) = M.keys m

entry :: Text -> Entry
entry t =
  Entry
    { entryLines = T.count "\n" t
    , entryBytes = TU.lengthWord8 t
    , entryTops = either (const Nothing) Just (SelfHosted.parse t)
    , entrySyntax = syntax
    , entryOutline = outlinePart t (fst syntax)
    }
  where
    syntax = S.parseSyntaxRecover t

-- Parsing ------------------------------------------------------------------------------

-- | The results of 'parseFragments'. The fields are computed when used.
data Parsed = Parsed
  { parsedTops :: Either [Diagnostic] [Top]
  -- ^ The same as 'Peg.Grammar.Parser.parseTops' of the text.
  , parsedSyntax :: (SyntaxNode, [SyntaxError])
  -- ^ The syntax tree and the syntax errors of the recovering parse of the
  -- text (ADR 0035), the same as a parse of the whole text, except for the
  -- expected sets of the errors ('syntaxErrorExpected'), which are not
  -- kept.
  , parsedOutline :: Outline
  -- ^ The same as 'Peg.Grammar.Outline.outline' of the text.
  , parsedFragments :: Fragments
  -- ^ The table for the next version: the fragments of this one.
  , parsedNew :: Int
  -- ^ How many fragments were not in the table, and are parsed.
  }

-- | Parse a text by its fragments, reusing those in the table.
parseFragments :: Fragments -> Text -> Parsed
parseFragments (Fragments old) src =
  Parsed
    { parsedTops = tops
    , parsedSyntax = syntax
    , parsedOutline = outlined
    , parsedFragments = Fragments (M.fromList entries)
    , parsedNew = length [() | t <- frags, not (M.member t old)]
    }
  where
    frags = splitFragments src
    entries = [(t, fromMaybe (entry t) (M.lookup t old)) | t <- frags]
    -- The line and byte offsets of each fragment.
    starts xs = scanl (\(l, b) e -> (l + entryLines e, b + entryBytes e)) (0, 0) (map snd xs)
    tops = case traverse (entryTops . snd) entries of
      Just tss -> Right (concat (zipWith (\(l, _) ts -> map (shiftTop l) ts) (starts entries) tss))
      -- The error of the whole parse, which a fragment cannot see.
      Nothing -> parseTops src
    groups = joined entries
    syntax
      | null entries = parseSyntaxWhole src
      | otherwise = (concatSyntax S.syntaxKindFile (map (fst . entrySyntax . snd) groups), errors)
    errors = concat (zipWith (\at (_, e) -> map (shiftError at) (snd (entrySyntax e))) (starts groups) groups)
    outlined
      | null entries = outlineFromTree src syntax
      | otherwise = joinOutline src (zipWith (\(l, _) (_, e) -> shiftOutlinePart l (entryOutline e)) (starts groups) groups) errors

-- The fragments for the recovering parse: a fragment is joined with the
-- next one when the parse of the whole text could read across their
-- boundary. That is when the fragment has an error in the spaces and
-- comments at its end, where the whole parse sees the next fragment and
-- may go on or skip it, or an error and an open bracket or string (see
-- 'open'); or when the next fragment does not start with a
-- directive or with a declaration up to its :: or <- without an error,
-- since an item of the previous rule can be read there.
joined :: [(Text, Entry)] -> [(Text, Entry)]
joined (x : y : rest)
  | errorAtEnd x || not (startsItem y) = joined ((fst x <> fst y, entry (fst x <> fst y)) : rest)
  | otherwise = x : joined (y : rest)
joined xs = xs

errorAtEnd :: (Text, Entry) -> Bool
errorAtEnd (t, e) = case snd (entrySyntax e) of
  [] -> False
  errs -> open t || any (\err -> trivia (TU.dropWord8 (fst (syntaxErrorRange err)) t)) errs
  where
    trivia s = case T.uncons (T.dropWhile isSpace s) of
      Nothing -> True
      Just ('#', r) -> trivia (T.dropWhile (/= '\n') r)
      Just _ -> False

-- Whether a text leaves a bracket, a string or a verbatim block open at
-- its end. Haskell code, its strings and verbatim blocks can span lines:
-- in a fragment with an error, the parse may have read an open one up to
-- the end of the fragment, where the parse of the whole text could find
-- its end, and read the fragment differently. The check is lexical, and
-- errs on the side of open: a quote closed on its line is a literal.
open :: Text -> Bool
open = go (0 :: Int) . T.unpack
  where
    go d s = case s of
      [] -> d > 0
      '%' : '{' : rest -> case T.breakOn "}%" (T.pack rest) of
        (_, r) | T.null r -> True
        (_, r) -> go d (T.unpack (T.drop 2 r))
      '"' : rest -> string d rest
      '\'' : rest | Just rest' <- quoted rest -> go d rest'
      c : rest
        | c `elem` ("([{" :: String) -> go (d + 1) rest
        | c `elem` (")]}" :: String) -> go (max 0 (d - 1)) rest
        | otherwise -> go d rest
    string d s = case s of
      [] -> True
      '\\' : _ : rest -> string d rest
      '"' : rest -> go d rest
      _ : rest -> string d rest
    -- The text after a quote closed on the same line.
    quoted s = case s of
      [] -> Nothing
      '\n' : _ -> Nothing
      '\\' : _ : rest -> quoted rest
      '\'' : rest -> Just rest
      _ : rest -> quoted rest

startsItem :: (Text, Entry) -> Bool
startsItem (t, e)
  | "%" `T.isPrefixOf` t = True
  | otherwise = case syntaxChildrenWithTokens root of
      NodeElement n : _
        | syntaxKind n == S.syntaxKindDeclaration
        , Just end <- listToMaybe [snd (tokenRange k) | TokenElement k <- syntaxChildrenWithTokens n, tokenKind k == textKind, any (`T.isPrefixOf` tokenText k) ["::", "<-"]] ->
            all (\err -> fst (syntaxErrorRange err) >= end) errs
      _ -> False
  where
    (root, errs) = entrySyntax e

shiftError :: (Int, Int) -> SyntaxError -> SyntaxError
shiftError (l, b) err =
  let (s, e) = syntaxErrorRange err
      p = syntaxErrorPos err
   in err
        { syntaxErrorRange = (s + b, e + b)
        , syntaxErrorPos = p {posOffset = posOffset p + b, posLine = posLine p + l}
        }

-- | The recovering parse of a whole text, which 'parsedSyntax' equals. For
-- tests.
parseSyntaxWhole :: Text -> (SyntaxNode, [SyntaxError])
parseSyntaxWhole = S.parseSyntaxRecover

-- | The name of a kind of the syntax tree of the notation, for
-- 'Peg.Runtime.Syntax.debugTree'.
syntaxKindName :: SyntaxKind -> Text
syntaxKindName = S.nameOfSyntaxKind

-- Locations ------------------------------------------------------------------------------

-- Move an item down by a number of lines. A fragment starts at the start of
-- a line, so the columns stay.
shiftTop :: Int -> Top -> Top
shiftTop 0 top = top
shiftTop d top = case top of
  TDirective l n al a -> TDirective (loc l) n (loc al) a
  TVerbatim l b -> TVerbatim (loc l) b
  TAnnot l n ps tps ty -> TAnnot (loc l) n [p {paramType = located (paramType p)} | p <- ps] tps (located ty)
  TDef l n tps as -> TDef (loc l) n tps (map alt as)
  where
    loc (Loc a b) = Loc (a + d) b
    located (Located l x) = Located (loc l) x
    alt (Alt l is act) = Alt (loc l) (map item is) (fmap located act)
    item (Item l b e) = Item (loc l) b (expr e)
    expr e = case e of
      ERef l n as -> ERef (loc l) n (map located as)
      EGroup g -> EGroup (map (map item) g)
      EStar x -> EStar (expr x)
      EPlus x -> EPlus (expr x)
      EOpt x -> EOpt (expr x)
      EAnd x -> EAnd (expr x)
      ENot x -> ENot (expr x)
      ECapture x -> ECapture (expr x)
      ELabel l x n -> ELabel (loc l) (expr x) n
      EPred b x -> EPred b (located x)
      ETemplate l n es as -> ETemplate (loc l) n (map expr es) (map located as)
      EDiscard x -> EDiscard (expr x)
      ELit {} -> e
      EClass {} -> e
      EAny -> e
