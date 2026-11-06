{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | What the language server knows of a grammar, read with error recovery
-- so that it is there while the grammar is being edited (ADR 0035): the
-- highlights, the declarations of rules, the references to rules, and the
-- syntax errors.
--
-- 'outline' never fails: the parser recovers from syntax errors (ADR 0021),
-- so a grammar in the middle of an edit still has its declarations and
-- references. The language server (@Peg.Lsp.Server@ in @peg-lsp@) answers
-- go to definition, references, hover, document symbols and semantic
-- tokens from it:
--
-- @
-- let o = outline src
--     defs = [declNameStart d | d <- outlineDeclarations o, declName d == \"Expr\", declKind d == Definition]
-- @
module Peg.Grammar.Outline
  ( Outline (..)
  , Declaration (..)
  , DeclarationKind (..)
  , Reference (..)
  , outline
  , outlineFromTree
  , OutlinePart
  , outlinePart
  , shiftOutlinePart
  , joinOutline
  , recoveredText
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import Data.Char (isSpace)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Peg.Grammar (Diagnostic (..), Loc (..))
import Peg.Grammar.Highlight
import Peg.Grammar.Parser (labelMessage)
import qualified Peg.Grammar.SelfHostedSyntax as S
import Peg.Runtime (Pos (..), SyntaxError (..))
import Peg.Runtime.Syntax

-- | What 'outline' finds in a grammar.
data Outline = Outline
  { outlineHighlights :: [Highlight]
  -- ^ The highlights of 'Peg.Grammar.Highlight.treeHighlights', leaving
  -- out the ranges that recovery skipped.
  , outlineDeclarations :: [Declaration]
  -- ^ The type annotations and definitions of rules, in source order.
  , outlineReferences :: [Reference]
  -- ^ Rule references, template calls and rule names in directives.
  , outlineSyntaxErrors :: [Diagnostic]
  -- ^ Every syntax error that recovery found, in source order, with the
  -- messages of 'Peg.Grammar.Parser.parseGrammar'.
  }
  deriving (Eq, Show)

-- | Which part of a rule a t'Declaration' is.
data DeclarationKind
  = -- | The type annotation, @Name :: Type@.
    Annotation
  | -- | The definition, @Name <- ...@.
    Definition
  deriving (Eq, Show)

-- | A type annotation or a definition of a rule.
data Declaration = Declaration
  { declName :: Text
  -- ^ The name of the rule.
  , declKind :: DeclarationKind
  , declTemplateParams :: Maybe [Text]
  -- ^ The parameters of a template (ADR 0031). 'Nothing' for other rules.
  , declNameStart :: Loc
  -- ^ The start of the name.
  , declNameEnd :: Loc
  -- ^ The location just after the name.
  , declStart :: Loc
  -- ^ The start of the declaration.
  , declEnd :: Loc
  -- ^ The end of its last token, before the comments and spaces after it.
  , declText :: Text
  -- ^ Its source, up to the end.
  }
  deriving (Eq, Show)

-- | A use of a rule's name: a reference to a rule, a call of a template,
-- or a rule named in a directive such as @%entry@ or @%recover@. A
-- reference to a template parameter inside the template is also listed.
data Reference = Reference
  { refName :: Text
  -- ^ The name as written.
  , refStart :: Loc
  -- ^ The start of the name.
  , refEnd :: Loc
  -- ^ The location just after the name.
  }
  deriving (Eq, Show)

-- | The outline of a grammar. Every text has one, whether or not it is a
-- valid grammar.
outline :: Text -> Outline
outline src = outlineFromTree src (S.parseSyntaxRecover src)

-- | The outline of a grammar from its syntax tree with recovery and the
-- errors that recovery found, as the recovering parse of the notation's
-- grammar returns them.
outlineFromTree :: Text -> (SyntaxNode, [SyntaxError]) -> Outline
outlineFromTree src (root, errors) = joinOutline src [outlinePart src root] errors

-- | What 'outline' finds in a part of a grammar made of whole top-level
-- items, apart from the syntax errors. "Peg.Grammar.Incremental" keeps one
-- for each top-level fragment, and joins those of a version with
-- 'joinOutline' (ADR 0071).
data OutlinePart = OutlinePart
  { partHighlights :: [Highlight]
  , partDeclarations :: [Declaration]
  , partRuleReferences :: [Reference]
  , partDirectiveReferences :: [Reference]
  }

-- | The outline part of a text from its syntax tree with recovery.
outlinePart :: Text -> SyntaxNode -> OutlinePart
outlinePart src root =
  OutlinePart
    { partHighlights = hs
    , partDeclarations = declarations root
    , partRuleReferences = [Reference (slice h) (hlStart h) (hlEnd h) | h <- hs, hlKind h == HRuleReference]
    , -- The rule names in the arguments of directives (ADR 0069).
      partDirectiveReferences = [Reference (slice h) (hlStart h) (hlEnd h) | h <- hs, hlKind h == HDirectiveRule]
    }
  where
    hs = treeHighlights root
    lines' = T.lines src
    slice h = sliceText lines' (hlStart h) (hlEnd h)

-- | An outline part moved down by a number of lines. A part that starts at
-- the start of a line keeps its columns.
shiftOutlinePart :: Int -> OutlinePart -> OutlinePart
shiftOutlinePart 0 p = p
shiftOutlinePart d (OutlinePart hs ds rs drs) =
  OutlinePart
    [h {hlStart = down (hlStart h), hlEnd = down (hlEnd h)} | h <- hs]
    [x {declNameStart = down (declNameStart x), declNameEnd = down (declNameEnd x), declStart = down (declStart x), declEnd = down (declEnd x)} | x <- ds]
    (map ref rs)
    (map ref drs)
  where
    down (Loc l c) = Loc (l + d) c
    ref r = r {refStart = down (refStart r), refEnd = down (refEnd r)}

-- | The outline of a text from the parts of its consecutive pieces, with
-- their locations in the text, and the syntax errors of the text.
joinOutline :: Text -> [OutlinePart] -> [SyntaxError] -> Outline
joinOutline src parts errors =
  Outline
    { outlineHighlights = concatMap partHighlights parts
    , outlineDeclarations = concatMap partDeclarations parts
    , outlineReferences = concatMap partRuleReferences parts ++ concatMap partDirectiveReferences parts
    , outlineSyntaxErrors = map (syntaxError src) (distinct errors)
    }
  where
    -- An error right after the range that the recovery of the previous one
    -- skipped follows from it: the construct the recovery ended is still
    -- incomplete.
    bytes = TE.encodeUtf8 src
    distinct (a : b : rest)
      | BC.all isSpace (BS.take (fst (syntaxErrorRange b) - snd (syntaxErrorRange a)) (BS.drop (snd (syntaxErrorRange a)) bytes)) = distinct (a : rest)
      | otherwise = a : distinct (b : rest)
    distinct es = es

-- | The text of the syntax tree that recovery builds, which is always the
-- input (ADR 0021). For tests.
recoveredText :: Text -> Text
recoveredText = syntaxText . fst . S.parseSyntaxRecover

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
