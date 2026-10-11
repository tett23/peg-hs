{-# LANGUAGE OverloadedStrings #-}

-- | Turning the top-level items of a grammar file into a 'Grammar'. Shared
-- by the hand-written parser and the self-hosted one.
module Peg.Grammar.Assemble
  ( Top (..)
  , assemble
  , toParam
  , isValidIdent
  , isIdentStart
  , isIdentChar
  , advanceLoc
  , verbatimBody
  , directiveArg
  ) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isSpace)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar

-- | A top-level item of a grammar file.
data Top
  = TDirective Loc Text Text
  | TVerbatim Loc Text
  | TAnnot Loc Text [Param] (Located Text)
  | TDef Loc Text [Alt]
  deriving (Eq, Show)

isIdentStart :: Char -> Bool
isIdentStart c = isAlpha c || c == '_'

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''

isValidIdent :: Text -> Bool
isValidIdent t = case T.uncons t of
  Just (c, rest) -> isIdentStart c && T.all isIdentChar rest
  Nothing -> False

advanceLoc :: Loc -> Text -> Loc
advanceLoc = T.foldl' step
  where
    step (Loc l _) '\n' = Loc (l + 1) 1
    step (Loc l c) _ = Loc l (c + 1)

-- | A parameter @name :: Type@ from an argument chunk.
toParam :: Located Text -> Either Text Param
toParam (Located l t) = case T.breakOn "::" t of
  (n, rest)
    | not (T.null rest)
    , let name = T.strip n
    , isValidIdent name ->
        let afterSep = T.drop 2 rest
            lead = T.takeWhile isSpace afterSep
            tyLoc = advanceLoc l (n <> "::" <> lead)
            ty = T.strip afterSep
         in if T.null ty then Left "expected a parameter type" else Right (Param name (Located tyLoc ty))
  _ -> Left "expected a parameter of the form name :: Type"

-- | The body of a @%{ ... }%@ block that starts at the given location: a
-- leading newline moves the block to the next line, and surrounding
-- whitespace is removed.
verbatimBody :: Loc -> Text -> (Loc, Text)
verbatimBody l body =
  let (start, text) = case T.uncons body of
        Just ('\n', rest) -> (Loc (locLine l + 1) 1, rest)
        _ -> (l, T.stripStart body)
   in (start, T.stripEnd text)

-- | The argument of a directive from the rest of its line. A comment ends
-- the argument, except for @%env@, whose type may contain @#@.
directiveArg :: Text -> Text -> Text
directiveArg name raw = T.strip (if name == "env" then raw else T.takeWhile (/= '#') raw)

-- | Check the top-level items and build the grammar.
assemble :: [Top] -> Either [Diagnostic] Grammar
assemble items =
  case errors of
    [] -> case moduleName of
      Just m ->
        Right
          Grammar
            { grammarModule = m
            , grammarStart = single "start"
            , grammarEntries = [Located l a | TDirective l "entry" a <- items]
            , grammarExports = concat [splitExports l a | TDirective l "export" a <- items]
            , grammarEnv = single "env"
            , grammarTabstop = tabstop
            , grammarNoMemo = [Located l a | TDirective l "nomemo" a <- items]
            , grammarVerbatim = [Located l t | TVerbatim l t <- items]
            , grammarRules = rules
            }
      Nothing -> Left [Diagnostic (Loc 1 1) "missing %module directive"]
    es -> Left (sortOn diagLoc es)
  where
    directives = [(l, n, a) | TDirective l n a <- items]
    known = ["module", "start", "entry", "export", "env", "tabstop", "nomemo"]
    single n = case [Located l a | (l, n', a) <- directives, n' == n] of
      x : _ -> Just x
      [] -> Nothing
    moduleName = single "module"
    tabstop = case single "tabstop" of
      Just (Located l a) | T.all isDigit a, not (T.null a) -> Just (Located l (read (T.unpack a)))
      _ -> Nothing
    annots = M.fromListWith (flip (++)) [(n, [(l, ps, ty)]) | TAnnot l n ps ty <- items]
    defs = [(l, n, alts) | TDef l n alts <- items]
    defCounts = M.fromListWith (+) [(n, 1 :: Int) | (_, n, _) <- defs]
    rules =
      [ Rule n l ps ty alts
      | (l, n, alts) <- defs
      , Just ((_, ps, ty) : _) <- [M.lookup n annots]
      ]
    errors =
      [Diagnostic l ("unknown directive %" <> n) | (l, n, _) <- directives, n `notElem` known]
        ++ [ Diagnostic l ("duplicate %" <> n <> " directive")
           | n <- ["module", "start", "env", "tabstop"]
           , (l, _, _) : _ : _ <- [reverse [d | d@(_, n', _) <- directives, n' == n]]
           ]
        ++ [Diagnostic l ("%" <> n <> " needs an argument") | (l, n, a) <- directives, n `elem` known, T.null a]
        ++ [ Diagnostic l ("%" <> n <> " expects a rule name")
           | (l, n, a) <- directives
           , n `elem` ["start", "entry", "nomemo"]
           , not (T.null a)
           , not (isValidIdent a)
           ]
        ++ [ Diagnostic l "%tabstop expects a positive integer"
           | Just (Located l a) <- [single "tabstop"]
           , not (T.all isDigit a) || T.null a || T.all (== '0') a
           ]
        ++ [ Diagnostic l ("rule " <> n <> " has no type annotation")
           | (l, n, _) <- defs
           , not (M.member n annots)
           ]
        ++ [ Diagnostic l ("rule " <> n <> " has a type annotation but no definition")
           | (n, (l, _, _) : _) <- M.toList annots
           , not (M.member n defCounts)
           ]
        ++ [ Diagnostic l ("duplicate type annotation for " <> n)
           | (n, _ : (l, _, _) : _) <- M.toList annots
           ]
        ++ [ Diagnostic l ("duplicate definition of " <> n)
           | (n, c) <- M.toList defCounts
           , c > 1
           , (l, _, _) : _ <- [drop 1 [d | d@(_, n', _) <- defs, n' == n]]
           ]
        ++ [Diagnostic (Loc 1 1) "the grammar has no rules" | null defs, isJust moduleName]

-- Split export items at top-level commas.
splitExports :: Loc -> Text -> [Located Text]
splitExports l0 t = go l0 (T.unpack t) (0 :: Int) [] []
  where
    go l [] _ cur acc = reverse (finish l cur acc)
    go l (c : cs) d cur acc
      | c == ',' && d == 0 = go (adv l c) cs d [] (finish l cur acc)
      | c `elem` ("([" :: String) = go (adv l c) cs (d + 1) (c : cur) acc
      | c `elem` (")]" :: String) = go (adv l c) cs (d - 1) (c : cur) acc
      | otherwise = go (adv l c) cs d (c : cur) acc
    adv (Loc ln col) _ = Loc ln (col + 1)
    finish l cur acc =
      let s = T.strip (T.pack (reverse cur))
       in if T.null s then acc else Located (Loc (locLine l) (locColumn l - length cur)) s : acc
