{-# LANGUAGE OverloadedStrings #-}

-- | Writing out the default constructor names of the rules whose types are
-- generated (ADR 0075). A default name, such as @Expr2@, depends on the
-- order of the alternatives; written as @\@Expr2@, it stays when the
-- alternatives change. The generated code is the same with the names
-- written as without them.
--
-- The language server offers the edits of a rule as a code action:
--
-- @
-- [(rule, edits) | (rule, edits) <- constructorNameEdits src, rule == \"Expr\"]
-- @
module Peg.Grammar.Constructors
  ( constructorNameEdits
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import Peg.Grammar
import Peg.Grammar.LabelInsertion (Edit (..))
import Peg.Grammar.Parser (parseGrammar)
import qualified Peg.Grammar.SelfHostedSyntax as S
import Peg.Grammar.Templates (expandTemplates)
import Peg.Grammar.Types
import Peg.Runtime (Pos (..))
import Peg.Runtime.Syntax

-- | For each rule whose type is generated and that has an alternative
-- without a constructor name, in source order: the rule, and the edits
-- that write @ \@Name@ with the default name at the end of each such
-- alternative. Empty for a grammar with an error that stops the
-- classification.
constructorNameEdits :: Text -> [(Text, [Edit])]
constructorNameEdits src = case (parseGrammar src >>= expandTemplates, S.parseSyntax src) of
  (Right g, Right root) ->
    let c = classify g
        types = M.fromList [(dataRule d, d) | d <- classDataTypes c, not (S.member (dataRule d) (classUnknown c))]
     in [ (name, edits)
        | (name, alts) <- definitions root
        , Just d <- [M.lookup name types]
        , length alts == length (dataConstructors d)
        , let edits = [Edit at (" @" <> conName con) | ((at, named), con) <- zip alts (dataConstructors d), not named]
        , not (null edits)
        ]
  _ -> []

kindOf :: SyntaxNode -> Text
kindOf = S.nameOfSyntaxKind . syntaxKind

-- The definitions of rules: the name, and for each alternative where its
-- name goes and whether it has one.
definitions :: SyntaxNode -> [(Text, [(Loc, Bool)])]
definitions root =
  [ (name, map alternative (alts n))
  | n <- syntaxChildren root
  , kindOf n == "Declaration"
  , any (\t -> tokenText t == "<-") [t | TokenElement t <- syntaxChildrenWithTokens n]
  , name : _ <- [[tokenText t | TokenElement t <- syntaxChildrenWithTokens n, S.nameOfSyntaxKind (tokenKind t) == "Ident"]]
  ]
  where
    alts n = concatMap altsIn (syntaxChildren n)
    altsIn n = case kindOf n of
      "Alt" -> [n]
      "Alts" -> concatMap altsIn (syntaxChildren n)
      "MoreAlt" -> concatMap altsIn (syntaxChildren n)
      _ -> []
    -- After the last token that is not a space or a comment, or at the
    -- start of an empty alternative.
    alternative a =
      let significant = [t | t <- syntaxTokens a, S.nameOfSyntaxKind (tokenKind t) `notElem` ["SpaceChar", "Comment"]]
          at = case reverse significant of
            t : _ -> snd (tokenRange t)
            [] -> fst (syntaxRange a)
       in (loc at, any ((== "Constructor") . kindOf) (syntaxChildren a))
    loc o = let p = syntaxPos root o in Loc (posLine p) (posColumn p)
