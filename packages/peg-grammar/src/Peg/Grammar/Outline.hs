{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | What the language server knows of a grammar, read with error recovery
-- so that it is there while the grammar is being edited (ADR 0035): the
-- highlights, the declarations of rules, the references to rules, and the
-- syntax errors.
module Peg.Grammar.Outline
  ( Outline (..)
  , Declaration (..)
  , DeclarationKind (..)
  , Reference (..)
  , outline
  , recoveredText
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import Data.Char (isSpace)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Peg.Grammar (Diagnostic (..), Loc (..))
import Peg.Grammar.Assemble (isIdentChar)
import Peg.Grammar.Highlight
import Peg.Grammar.Parser (labelMessage)
import qualified Peg.Grammar.SelfHostedSyntax as S
import Peg.Runtime (Pos (..), SyntaxError (..))
import Peg.Runtime.Syntax

data Outline = Outline
  { outlineHighlights :: [Highlight]
  , outlineDeclarations :: [Declaration]
  , outlineReferences :: [Reference]
  -- ^ Rule references, template calls and rule names in directives.
  , outlineSyntaxErrors :: [Diagnostic]
  -- ^ Every syntax error that recovery found, in source order, with the
  -- messages of 'Peg.Grammar.Parser.parseGrammar'.
  }
  deriving (Eq, Show)

data DeclarationKind = Annotation | Definition
  deriving (Eq, Show)

-- | A type annotation or a definition of a rule.
data Declaration = Declaration
  { declName :: Text
  , declKind :: DeclarationKind
  , declTemplateParams :: Maybe [Text]
  -- ^ The parameters of a template (ADR 0031).
  , declNameStart :: Loc
  , declNameEnd :: Loc
  , declStart :: Loc
  , declEnd :: Loc
  -- ^ The end of its last token, before the comments and spaces after it.
  , declText :: Text
  -- ^ Its source, up to the end.
  }
  deriving (Eq, Show)

data Reference = Reference
  { refName :: Text
  , refStart :: Loc
  , refEnd :: Loc
  }
  deriving (Eq, Show)

-- | The outline of a grammar. Every text has one.
outline :: Text -> Outline
outline src =
  let (root, errors) = S.parseSyntaxRecover src
      hs = treeHighlights root
   in Outline
        { outlineHighlights = hs
        , outlineDeclarations = declarations root
        , outlineReferences = [Reference (slice h) (hlStart h) (hlEnd h) | h <- hs, hlKind h == HRuleReference] ++ directiveReferences hs
        , outlineSyntaxErrors = map (syntaxError src) (distinct errors)
        }
  where
    lines' = T.lines src
    -- An error right after the range that the recovery of the previous one
    -- skipped follows from it: the construct the recovery ended is still
    -- incomplete.
    bytes = TE.encodeUtf8 src
    distinct (a : b : rest)
      | BC.all isSpace (BS.take (fst (syntaxErrorRange b) - snd (syntaxErrorRange a)) (BS.drop (snd (syntaxErrorRange a)) bytes)) = distinct (a : rest)
      | otherwise = a : distinct (b : rest)
    distinct es = es
    slice h = sliceText lines' (hlStart h) (hlEnd h)
    directiveReferences hs =
      concat
        [ [ Reference w (Loc l (c + off)) (Loc l (c + off + T.length w))
          | (k, (off, w)) <- zip [0 :: Int ..] (wordsAt (slice a))
          , T.all isIdentChar w
          , if name == "%recover" then k == 1 else name /= "%recover"
          ]
        | (d, a) <- zip hs (drop 1 hs)
        , hlKind d == HDirective
        , hlKind a == HDirectiveArgument
        , let name = slice d
        , name `elem` ["%start", "%entry", "%nomemo", "%token", "%trivia", "%inline", "%recover"]
        , let Loc l c = hlStart a
        ]

-- | The text of the syntax tree that recovery builds, which is always the
-- input (ADR 0021). For tests.
recoveredText :: Text -> Text
recoveredText = syntaxText . fst . S.parseSyntaxRecover

-- The words of a text with their offsets in code points.
wordsAt :: Text -> [(Int, Text)]
wordsAt = go 0
  where
    go off t
      | T.null t = []
      | isSpace (T.head t) = let (s, rest) = T.span isSpace t in go (off + T.length s) rest
      | otherwise = let (w, rest) = T.break isSpace t in (off, w) : go (off + T.length w) rest

sliceText :: [Text] -> Loc -> Loc -> Text
sliceText ls (Loc l1 c1) (Loc l2 c2)
  | l1 == l2 = T.take (c2 - c1) (T.drop (c1 - 1) (line l1))
  | otherwise = T.intercalate "\n" ([T.drop (c1 - 1) (line l1)] ++ map line [l1 + 1 .. l2 - 1] ++ [T.take (c2 - 1) (line l2)])
  where
    line n = case drop (n - 1) ls of
      x : _ -> x
      [] -> ""

kindOf :: SyntaxNode -> Text
kindOf = S.nameOfSyntaxKind . syntaxKind

loc :: SyntaxNode -> Int -> Loc
loc root o = let p = syntaxPos root o in Loc (posLine p) (posColumn p)

declarations :: SyntaxNode -> [Declaration]
declarations root = concatMap go (syntaxChildren root)
  where
    go n
      | kindOf n == "Declaration" = maybe [] pure (declaration n)
      | otherwise = []
    declaration n = do
      let es = syntaxChildrenWithTokens n
          significant = [t | t <- syntaxTokens n, S.nameOfSyntaxKind (tokenKind t) `notElem` ["SpaceChar", "Comment"]]
      nameTok <- case [t | TokenElement t <- es, S.nameOfSyntaxKind (tokenKind t) == "Ident"] of
        t : _ -> Just t
        [] -> Nothing
      lastTok <- case reverse significant of
        t : _ -> Just t
        [] -> Nothing
      let kind = if any (\case TokenElement t -> tokenText t == "<-"; _ -> False) es then Definition else Annotation
          params = case [m | NodeElement m <- es, kindOf m == "TemplateParams"] of
            m : _ -> Just [tokenText t | NodeElement p <- syntaxChildrenWithTokens m, kindOf p == "TemplateParam", TokenElement t <- take 1 (syntaxChildrenWithTokens p)]
            [] -> Nothing
          (start, _) = syntaxRange n
          end = snd (tokenRange lastTok)
      pure
        Declaration
          { declName = tokenText nameTok
          , declKind = kind
          , declTemplateParams = params
          , declNameStart = loc root (fst (tokenRange nameTok))
          , declNameEnd = loc root (snd (tokenRange nameTok))
          , declStart = loc root start
          , declEnd = loc root end
          , declText = T.concat (map tokenText (takeWhile (\t -> fst (tokenRange t) < end) (syntaxTokens n)))
          }

syntaxError :: Text -> SyntaxError -> Diagnostic
syntaxError src e =
  let p = syntaxErrorPos e
      at = case drop (posLine p - 1) (T.lines src) of
        l : _ -> fmap fst (T.uncons (T.drop (posColumn p - 1) l))
        [] -> Nothing
   in Diagnostic (Loc (posLine p) (posColumn p)) (maybe "unexpected input" (labelMessage at) (syntaxErrorLabel e))
