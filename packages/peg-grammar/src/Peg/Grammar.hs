{-# LANGUAGE OverloadedStrings #-}

-- | The abstract syntax of @.peg@ grammar files.
--
-- Use "Peg.Grammar.Parser" to read a grammar and "Peg.Grammar.Check" to
-- validate it.
module Peg.Grammar
  ( -- * Locations
    Loc (..)
  , Located (..)
    -- * Grammars
  , Grammar (..)
  , Rule (..)
  , Param (..)
  , Alt (..)
  , Item (..)
  , Expr (..)
    -- * Diagnostics
  , Diagnostic (..)
  , renderDiagnostic
  ) where

import Data.Text (Text)
import qualified Data.Text as T

-- | A location in a grammar file. Lines and columns start at 1, and each
-- code point counts as one column.
data Loc = Loc
  { locLine :: !Int
  , locColumn :: !Int
  }
  deriving (Eq, Ord, Show)

-- | A value with the location where it starts.
data Located a = Located
  { locOf :: !Loc
  , unLoc :: a
  }
  deriving (Eq, Show)

-- | A whole grammar file.
data Grammar = Grammar
  { grammarModule :: Located Text
  -- ^ @%module@: the name of the generated module.
  , grammarStart :: Maybe (Located Text)
  -- ^ @%start@: the start rule. Defaults to the first rule.
  , grammarEntries :: [Located Text]
  -- ^ @%entry@: additional rules with entry points.
  , grammarExports :: [Located Text]
  -- ^ @%export@: export items, as written.
  , grammarEnv :: Maybe (Located Text)
  -- ^ @%env@: the type of the parse environment.
  , grammarTabstop :: Maybe (Located Int)
  -- ^ @%tabstop@: the tab stop used by @_col@.
  , grammarNoMemo :: [Located Text]
  -- ^ @%nomemo@: rules that are not memoised.
  , grammarLanguages :: [Located Text]
  -- ^ @%language@: language extensions of the generated module, in order.
  , grammarSyntax :: Maybe Loc
  -- ^ @%syntax@: also generate a lossless syntax tree.
  , grammarTokens :: [Located Text]
  -- ^ @%token@: rules that become single tokens in the syntax tree.
  , grammarTrivia :: [Located Text]
  -- ^ @%trivia@: token rules that are trivia (whitespace, comments).
  , grammarInline :: [Located Text]
  -- ^ @%inline@: rules whose children are spliced into the caller's node.
  , grammarVerbatim :: [Located Text]
  -- ^ @%{ ... }%@ blocks, in order.
  , grammarRules :: [Rule]
  -- ^ Rules, in the order of their definitions.
  }
  deriving (Eq, Show)

-- | A rule: a type annotation together with a definition.
data Rule = Rule
  { ruleName :: Text
  , ruleLoc :: Loc
  -- ^ Where the definition starts.
  , ruleParams :: [Param]
  , ruleType :: Located Text
  -- ^ The result type, as written.
  , ruleAlts :: [Alt]
  }
  deriving (Eq, Show)

-- | A rule parameter.
data Param = Param
  { paramName :: Text
  , paramType :: Located Text
  }
  deriving (Eq, Show)

-- | An alternative of a rule: a sequence and an optional action.
data Alt = Alt
  { altLoc :: Loc
  , altItems :: [Item]
  , altAction :: Maybe (Located Text)
  }
  deriving (Eq, Show)

-- | An element of a sequence, with an optional binding.
data Item = Item
  { itemLoc :: Loc
  , itemBind :: Maybe Text
  , itemExpr :: Expr
  }
  deriving (Eq, Show)

-- | Parsing expressions.
data Expr
  = -- | A literal: the text to match and the literal as written.
    ELit Text Text
  | -- | A character class: inclusive ranges and the class as written.
    EClass [(Char, Char)] Text
  | -- | Any single character.
    EAny
  | -- | A reference to a rule, with arguments.
    ERef Loc Text [Located Text]
  | -- | A parenthesised choice of sequences.
    EGroup [[Item]]
  | EStar Expr
  | EPlus Expr
  | EOpt Expr
  | EAnd Expr
  | ENot Expr
  | -- | @$e@: the consumed text.
    ECapture Expr
  | -- | @e ^label@: reserved, not implemented.
    ELabel Loc Expr Text
  | -- | @&{ e }@ ('True') or @!{ e }@ ('False').
    EPred Bool (Located Text)
  deriving (Eq, Show)

-- | An error found in a grammar.
data Diagnostic = Diagnostic
  { diagLoc :: Loc
  , diagMessage :: Text
  }
  deriving (Eq, Show)

-- | Render as @file:line:column: error: message@.
renderDiagnostic :: FilePath -> Diagnostic -> Text
renderDiagnostic file (Diagnostic (Loc l c) msg) =
  T.concat [T.pack file, ":", T.pack (show l), ":", T.pack (show c), ": error: ", msg]
