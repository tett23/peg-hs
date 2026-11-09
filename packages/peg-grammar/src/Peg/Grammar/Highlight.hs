{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The kinds and ranges of the tokens of a grammar, from its lossless
-- syntax tree: for the editor grammars' consistency test (ADR 0034) and the
-- semantic tokens of the language server (ADR 0035).
--
-- 'highlights' reads a grammar that has no syntax error; 'treeHighlights'
-- works on any syntax tree of the notation, including the one that error
-- recovery builds, which is how "Peg.Grammar.Outline" uses it.
--
-- @
-- forM_ (fromMaybe [] (highlights src)) $ \\h ->
--   print (hlKind h, locLine (hlStart h), locColumn (hlStart h))
-- @
module Peg.Grammar.Highlight
  ( HighlightKind (..)
  , Highlight (..)
  , highlights
  , treeHighlights
  ) where

import Data.Char (isAlphaNum, isUpper)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar (Loc (..))
import Peg.Grammar.Assemble (directiveComment, isIdentChar, isValidIdent)
import qualified Peg.Grammar.SelfHostedSyntax as S
import Peg.Runtime (Pos (..))
import Peg.Runtime.Syntax

-- | What a range of the grammar is.
data HighlightKind
  = HComment
  | -- | @%name@.
    HDirective
  | -- | The argument of @%export@, @%env@, @%tabstop@, @%language@ and
    -- other directives, and a word of the arguments below that is not what
    -- its directive expects there.
    HDirectiveArgument
  | -- | The name of a rule in the argument of a directive: @%start@,
    -- @%entry@, @%nomemo@, @%token@, @%trivia@, @%inline@, the second
    -- argument of @%recover@ (ADR 0069) and the first of @%expect@
    -- (ADR 0089).
    HDirectiveRule
  | -- | The label in the argument of @%recover@, @%safe@ (ADR 0069) and
    -- @%message@ (ADR 0089).
    HDirectiveLabel
  | -- | The argument of @%module@ (ADR 0069).
    HModuleName
  | -- | The name of a rule in its annotation or definition.
    HRuleName
  | HRuleReference
  | -- | @<@ and @>@ of template parameters and arguments.
    HTemplateBracket
  | HTemplateParameter
  | -- | @name:@.
    HBinding
  | HLiteral
  | HClass
  | -- | @.@.
    HAny
  | -- | @<-@ and @::@.
    HDefinition
  | -- | @/@.
    HChoice
  | -- | @*@, @+@, @?@, @&@, @!@ and @$@.
    HOperator
  | -- | @^label@.
    HLabel
  | -- | The name of @\@Name@, a constructor name (ADR 0075).
    HConstructor
  | -- | A class name in the argument of @%deriving@ (ADR 0075).
    HClassName
  | -- | @_span@, @_env@ and @_col@ in Haskell code; inside an action, a
    -- predicate or arguments.
    HReservedBinding
  | -- | Haskell code: an action with its braces, a predicate's code with its
    -- closing brace, arguments, a type, a verbatim block.
    HAction
  | HPredicate
  | HArguments
  | HType
  | HVerbatim
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | A range: the start, and the end just after it, as locations with
-- columns counted in code points from 1.
data Highlight = Highlight
  { hlKind :: HighlightKind
  , hlStart :: Loc
  , hlEnd :: Loc
  }
  deriving (Eq, Show)

-- | The highlights of a grammar in source order, or 'Nothing' for a grammar
-- with a syntax error. Reserved bindings lie inside the ranges of Haskell
-- code; other ranges do not overlap.
highlights :: Text -> Maybe [Highlight]
highlights src = case S.parseSyntax src of
  Left _ -> Nothing
  Right root -> Just (treeHighlights root)

-- | The highlights of a syntax tree of the notation, leaving out the ranges
-- that error recovery skipped.
treeHighlights :: SyntaxNode -> [Highlight]
treeHighlights root = node root root

kindOf :: SyntaxNode -> Text
kindOf = S.nameOfSyntaxKind . syntaxKind

tokenKindName :: SyntaxToken -> Text
tokenKindName = S.nameOfSyntaxKind . tokenKind

loc :: SyntaxNode -> Int -> Loc
loc root o = let p = syntaxPos root o in Loc (posLine p) (posColumn p)

-- A range of bytes as a highlight.
range :: SyntaxNode -> HighlightKind -> (Int, Int) -> Highlight
range root k (a, b) = Highlight k (loc root a) (loc root b)

bytes :: Text -> Int
bytes = sum . map (\c -> let n = fromEnum c in if n < 0x80 then 1 else if n < 0x800 then 2 else if n < 0x10000 then 3 else 4) . T.unpack

node :: SyntaxNode -> SyntaxNode -> [Highlight]
node root n = case kindOf n of
  "ERROR" -> []
  "Directive" -> directive root n
  "Verbatim" -> [range root HVerbatim (syntaxRange n)]
  "Action" -> range root HAction (syntaxRange n) : reserved root n
  "PredCode" -> range root HPredicate (syntaxRange n) : reserved root n
  "CallArgs" -> range root HArguments (syntaxRange n) : reserved root n
  "ParamList" -> [range root HArguments (syntaxRange n)]
  "Binding" -> [range root HBinding (syntaxRange n)]
  "Constructor" -> [range root HConstructor (tokenRange t) | TokenElement t <- syntaxChildrenWithTokens n, tokenKindName t == "Ident"]
  "LabelPart" -> case [t | TokenElement t <- syntaxChildrenWithTokens n, tokenText t == "^"] of
    t : _ -> [range root HLabel (fst (tokenRange t), snd (syntaxRange n))]
    [] -> []
  "Declaration" -> declaration root n
  k -> concatMap (element root k) (syntaxChildrenWithTokens n)

element :: SyntaxNode -> Text -> SyntaxElement -> [Highlight]
element root parent = \case
  NodeElement n
    | kindOf n `elem` ["TemplateArgs", "TemplateParams"] -> concatMap (element root (kindOf n)) (syntaxChildrenWithTokens n)
    | kindOf n == "TemplateParam" -> [range root HTemplateParameter (tokenRange t) | TokenElement t <- syntaxChildrenWithTokens n, tokenKindName t == "Ident"] ++ [range root HDefinition (tokenRange t) | TokenElement t <- syntaxChildrenWithTokens n, tokenText t == "::"]
    | otherwise -> node root n
  TokenElement t -> case tokenKindName t of
    "Comment" -> [range root HComment (trimmed t)]
    "Lit1" -> [range root HLiteral (tokenRange t)]
    "Lit2" -> [range root HLiteral (tokenRange t)]
    "ClassLit" -> [range root HClass (tokenRange t)]
    "Ident" | parent == "Primary" -> [range root HRuleReference (tokenRange t)]
    "SpaceChar" -> []
    _ -> case tokenText t of
      "." | parent == "Primary" -> [range root HAny (tokenRange t)]
      "/" -> [range root HChoice (tokenRange t)]
      "<" | parent `elem` ["TemplateArgs", "TemplateParams"] -> [range root HTemplateBracket (tokenRange t)]
      ">" | parent `elem` ["TemplateArgs", "TemplateParams"] -> [range root HTemplateBracket (tokenRange t)]
      s
        | parent `elem` ["PrefixE", "PostOp"], Just (c, _) <- T.uncons s, c `elem` ("&!$*+?" :: String) ->
            [range root HOperator (fst (tokenRange t), fst (tokenRange t) + 1)]
        | otherwise -> []
  where
    trimmed t = let (a, _) = tokenRange t in (a, a + bytes (T.stripEnd (tokenText t)))

declaration :: SyntaxNode -> SyntaxNode -> [Highlight]
declaration root n = go True (syntaxChildrenWithTokens n)
  where
    go _ [] = []
    go first (e : rest) = case e of
      TokenElement t
        | tokenKindName t == "Ident", first -> range root HRuleName (tokenRange t) : go False rest
        | tokenText t `elem` ["::", "<-"] -> range root HDefinition (tokenRange t) : go False rest
        | tokenKindName t == "TypeText" ->
            let (a, _) = tokenRange t in range root HType (a, a + bytes (T.stripEnd (tokenText t))) : go False rest
      _ -> element root "Declaration" e ++ go first rest

-- @%name@, its argument and its comment.
directive :: SyntaxNode -> SyntaxNode -> [Highlight]
directive root n =
  let (start, _) = syntaxRange n
      text = syntaxText n
      (name, rest) = T.span isIdentChar (T.drop 1 text)
      nameEnd = start + 1 + bytes name
      lead = T.takeWhile (`elem` [' ', '\t']) rest
      raw = T.drop (T.length lead) rest
      argStart = nameEnd + bytes lead
      (arg, comment) = directiveComment name raw
      argText = T.stripEnd arg
      argEnd = argStart + bytes argText
      commentStart = argStart + bytes arg
      argument
        | name == "deriving" =
            [ range root (if isClassName w then HClassName else HDirectiveArgument) (argStart + off, argStart + off + bytes w)
            | (off, w) <- commaItems argText
            ]
        -- A name and a string (ADR 0089).
        | name `elem` ["expect", "message"] =
            let (w, afterName) = T.break blank argText
                gap = T.takeWhile blank afterName
                str = T.drop (T.length gap) afterName
                strStart = argStart + bytes w + bytes gap
                nameKind
                  | not (isValidIdent w) = HDirectiveArgument
                  | name == "expect" = HDirectiveRule
                  | otherwise = HDirectiveLabel
             in [range root nameKind (argStart, argStart + bytes w) | not (T.null w)]
                  ++ [range root (if "\"" `T.isPrefixOf` str then HLiteral else HDirectiveArgument) (strStart, strStart + bytes str) | not (T.null str)]
        | name `elem` wordDirectives =
            [ range root (wordKind name k w) (argStart + off, argStart + off + bytes w)
            | (k, (off, w)) <- zip [0 :: Int ..] (byteWords argText)
            ]
        | otherwise = [range root HDirectiveArgument (argStart, argEnd) | not (T.null argText)]
      blank c = c == ' ' || c == '\t'
   in [range root HDirective (start, nameEnd)]
        ++ argument
        ++ [range root HComment (commentStart, commentStart + bytes (T.stripEnd comment)) | not (T.null comment)]

-- The directives whose arguments are read word by word (ADR 0069).
wordDirectives :: [Text]
wordDirectives = ["module", "start", "entry", "nomemo", "token", "trivia", "inline", "recover", "safe"]

-- The kind of the k-th word of the argument of a directive; a word that
-- cannot be what the directive expects there stays an argument.
wordKind :: Text -> Int -> Text -> HighlightKind
wordKind name k w
  | name == "module", k == 0 = HModuleName
  | not (T.all isIdentChar w) = HDirectiveArgument
  | name `elem` ["start", "entry", "nomemo", "token", "trivia", "inline"] = HDirectiveRule
  | name == "recover", k == 0 = HDirectiveLabel
  | name == "recover", k == 1 = HDirectiveRule
  | name == "safe", k == 0 = HDirectiveLabel
  | otherwise = HDirectiveArgument

-- The items of a text separated by commas, without the spaces around
-- them, with their offsets in bytes.
commaItems :: Text -> [(Int, Text)]
commaItems = go 0
  where
    go off t
      | T.null t = []
      | otherwise =
          let (item, rest) = T.break (== ',') t
              lead = T.takeWhile blank item
              w = T.stripEnd (T.drop (T.length lead) item)
              next = off + bytes item + 1
           in [(off + bytes lead, w) | not (T.null w)] ++ (if T.null rest then [] else go next (T.drop 1 rest))
    blank c = c == ' ' || c == '\t'

-- Whether a word is a class name, which may be qualified.
isClassName :: Text -> Bool
isClassName w = not (T.null w) && all part (T.splitOn "." w)
  where
    part p = case T.uncons p of
      Just (c, rest) -> isUpper c && T.all isIdentChar rest
      Nothing -> False

-- The words of a text separated by spaces and tabs, with their offsets in
-- bytes.
byteWords :: Text -> [(Int, Text)]
byteWords = go 0
  where
    blank c = c == ' ' || c == '\t'
    go off t
      | T.null t = []
      | blank (T.head t) = let (s, rest) = T.span blank t in go (off + bytes s) rest
      | otherwise = let (w, rest) = T.break blank t in (off, w) : go (off + bytes w) rest

-- The reserved bindings in the code of a node.
reserved :: SyntaxNode -> SyntaxNode -> [Highlight]
reserved root n = go (fst (syntaxRange n)) (syntaxText n)
  where
    go off t
      | T.null t = []
      | identChar (T.head t) =
          let (w, rest) = T.span identChar t
           in [range root HReservedBinding (off, off + bytes w) | w `elem` ["_span", "_env", "_col"]] ++ go (off + bytes w) rest
      | otherwise = let (o, rest) = T.break identChar t in go (off + bytes o) rest
    identChar c = isAlphaNum c || c == '_' || c == '\''
