{-# LANGUAGE OverloadedStrings #-}

-- | The abstract syntax of @.hpeg@ grammar files, and the diagnostics that
-- the modules of this package report about them.
--
-- The other modules work on a t'Grammar' or on the source text:
--
-- * "Peg.Grammar.Parser" reads a grammar ('Peg.Grammar.Parser.parseGrammar').
-- * "Peg.Grammar.Templates" expands rule templates (ADR 0031).
-- * "Peg.Grammar.Check" checks the expanded grammar and analyses it for
--   the code generator.
-- * "Peg.Grammar.Labels" warns about labels that may change the language
--   (ADR 0028).
-- * "Peg.Grammar.Lint" warns about mistakes that are not errors (ADR 0033).
-- * "Peg.Grammar.Format" formats the source (ADR 0032).
-- * "Peg.Grammar.Highlight" and "Peg.Grammar.Outline" describe the source
--   for editors and the language server (ADR 0034, ADR 0035).
--
-- The checks of @peg-hs gen@ run in this order. Errors in the body of a
-- template are reported once for each call that expanded it, so
-- 'Peg.Grammar.Templates.templateNotes' adds the call to them:
--
-- @
-- import Peg.Grammar
-- import Peg.Grammar.Check (check)
-- import Peg.Grammar.Labels (labelWarnings)
-- import Peg.Grammar.Lint (lintGrammar)
-- import Peg.Grammar.Parser (parseGrammar)
-- import Peg.Grammar.Templates (expandTemplates, templateNotes)
--
-- -- The grammar as parsed and expanded, and the warnings about its labels.
-- checkGrammar :: Text -> Either [Diagnostic] (Grammar, Grammar, [Diagnostic])
-- checkGrammar src = do
--   g0 <- parseGrammar src
--   g <- either (Left . templateNotes g0) Right (expandTemplates g0)
--   _ <- either (Left . templateNotes g0) Right (check g)
--   pure (g0, g, templateNotes g0 (labelWarnings g))
-- @
--
-- 'Peg.Grammar.Lint.lintGrammar' takes the grammar as parsed (@g0@), and
-- @Peg.Codegen.generate@ (in the @peg-codegen@ package) generates a module
-- from it.
module Peg.Grammar
  ( -- * Locations
    Loc (..)
  , Located (..)
    -- * Grammars
  , Grammar (..)
  , Rule (..)
  , Param (..)
  , TemplateParam (..)
  , Alt (..)
  , Item (..)
  , Expr (..)
    -- * Diagnostics
  , Diagnostic (..)
  , renderDiagnostic
    -- * Names in generated modules
  , syntaxTypeName
  ) where

import Data.Char (isUpper, toUpper)
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

-- | A whole grammar file, as read by 'Peg.Grammar.Parser.parseGrammar'.
-- The directives are kept as written; whether they make sense together is
-- decided by 'Peg.Grammar.Check.check'.
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
  , grammarRecovers :: [(Located Text, Located Text)]
  -- ^ @%recover@: labels and their recovery rules.
  , grammarSafe :: [Located Text]
  -- ^ @%safe@: labels the author has checked to be safe (ADR 0028).
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
  , ruleTemplateParams :: [TemplateParam]
  -- ^ The parameters of a rule template (ADR 0031). Empty for other rules.
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

-- | A parameter of a rule template (ADR 0031): its name, and the type
-- variable of its value when the value is used.
data TemplateParam = TemplateParam
  { templateParamName :: Text
  , templateParamType :: Maybe Text
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
  | -- | @e ^label@: throw the label when @e@ fails (ADR 0021).
    ELabel Loc Expr Text
  | -- | @&{ e }@ ('True') or @!{ e }@ ('False').
    EPred Bool (Located Text)
  | -- | @Name<e, ...>@: a call of a rule template (ADR 0031).
    ETemplate Loc Text [Expr]
  | -- | An expression whose value is discarded. It does not appear in the
    -- notation: template expansion puts the arguments of untyped template
    -- parameters in it (ADR 0031).
    EDiscard Expr
  deriving (Eq, Show)

-- | A message about a location in a grammar: an error, or a warning such
-- as those of 'Peg.Grammar.Labels.labelWarnings'. The message is one line
-- of English without the location.
data Diagnostic = Diagnostic
  { diagLoc :: Loc
  , diagMessage :: Text
  }
  deriving (Eq, Show)

-- | Render as @file:line:column: error: message@, the form @peg-hs@ uses
-- for errors. The file name is written as given.
--
-- @
-- either (mapM_ (TIO.hPutStrLn stderr . renderDiagnostic \"Calc.hpeg\")) (const (pure ())) (parseGrammar src)
-- @
renderDiagnostic :: FilePath -> Diagnostic -> Text
renderDiagnostic file (Diagnostic (Loc l c) msg) =
  T.concat [T.pack file, ":", T.pack (show l), ":", T.pack (show c), ": error: ", msg]

-- | The name of the type of the syntax tree nodes of a rule, in a grammar
-- with @%syntax@ (ADR 0019): the rule name with its first letter made
-- upper case, and @Syntax@ after it. A rule name whose first letter has
-- no upper case, such as kanji, kana or @_@, gets @Rule'@ before it, since
-- a Haskell type name must start with an upper case letter (ADR 0053).
--
-- @
-- syntaxTypeName "expr" == "ExprSyntax"
-- syntaxTypeName "数式" == "Rule'数式Syntax"
-- @
syntaxTypeName :: Text -> Text
syntaxTypeName n = case T.uncons n of
  Just (c, rest) | isUpper (toUpper c) -> T.cons (toUpper c) rest <> "Syntax"
  _ -> "Rule'" <> n <> "Syntax"
