{-# LANGUAGE OverloadedStrings #-}

-- | The abstract syntax of @.hpeg@ grammar files, and the diagnostics that
-- the modules of this package report about them.
--
-- The other modules work on a t'Grammar' or on the source text:
--
-- * "Peg.Grammar.Parser" reads a grammar ('Peg.Grammar.Parser.parseGrammar').
-- * "Peg.Grammar.Import" puts the rules of the libraries that a grammar
--   imports into it (ADR 0092), and "Peg.Grammar.Import.Files" reads them.
-- * "Peg.Grammar.Templates" expands rule templates (ADR 0031).
-- * "Peg.Grammar.Check" checks the expanded grammar and analyses it for
--   the code generator.
-- * "Peg.Grammar.Types" decides the types of the rules without type
--   annotations and actions (ADR 0075).
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
  , diagnosticFile
  , importedPath
    -- * Names in generated modules
  , syntaxTypeName
    -- * Haskell code
  , codeVariables
  , reservedWords
  ) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isPunctuation, isSymbol, isUpper, toUpper)
import Data.Text (Text)
import qualified Data.Text as T

-- | A location in a grammar file. Lines and columns start at 1, and each
-- code point counts as one column.
--
-- The file is @0@ for the grammar itself, and @i@ for the library of the
-- @i@-th @%import@ of the grammar (ADR 0092): the parser makes locations
-- in the file @0@, and 'Peg.Grammar.Import.resolveImports' renumbers
-- those of the libraries it imports. Locations are ordered by file, line
-- and column.
data Loc = Loc
  { locFile :: !Int
  , locLine :: !Int
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
  -- ^ @%module@: the name of the generated module. Empty, at the location
  -- of @%library@, in a library (ADR 0092).
  , grammarImports :: [Located FilePath]
  -- ^ @%import@: the paths of the libraries, as written and in order, at
  -- the locations of the directives (ADR 0092).
  , grammarLibrary :: Maybe Loc
  -- ^ @%library@: the file is a library, whose rules other grammars
  -- import (ADR 0092).
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
  , grammarExpects :: [(Located Text, Located Text)]
  -- ^ @%expect@: rules and their display names in errors (ADR 0089). The
  -- name is decoded, at the location of its opening quote.
  , grammarMessages :: [(Located Text, Located Text)]
  -- ^ @%message@: labels and their messages in errors (ADR 0089). The
  -- message is decoded, at the location of its opening quote.
  , grammarDeriving :: Maybe (Located [Located Text])
  -- ^ @%deriving@: the classes that the generated types derive (ADR 0075),
  -- at the location of the directive. 'Nothing' without the directive:
  -- the types derive @Eq@ and @Show@. An empty list derives nothing.
  , grammarVerbatim :: [Located Text]
  -- ^ @%{ ... }%@ blocks, in order.
  , grammarRules :: [Rule]
  -- ^ Rules, in the order of their definitions.
  }
  deriving (Eq, Show)

-- | A rule: a definition together with its type annotation. A rule without
-- a type annotation has type @()@ (ADR 0066).
data Rule = Rule
  { ruleName :: Text
  , ruleLoc :: Loc
  -- ^ Where the definition starts.
  , ruleParams :: [Param]
  , ruleTemplateParams :: [TemplateParam]
  -- ^ The parameters of a rule template (ADR 0031). Empty for other rules.
  , ruleType :: Located Text
  -- ^ The result type, as written. For a rule without a type annotation,
  -- @()@ at the start of the definition.
  , ruleAnnotation :: Maybe Loc
  -- ^ Where the type annotation starts, or 'Nothing' for a rule without
  -- one (ADR 0066).
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

-- | An alternative of a rule: a sequence, an optional action, and an
-- optional constructor name @\@Name@ (ADR 0075).
data Alt = Alt
  { altLoc :: Loc
  , altItems :: [Item]
  , altAction :: Maybe (Located Text)
  , altConstructor :: Maybe (Located Text)
  -- ^ The name after @\@@, at the location of the name.
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
  | -- | @Name<e, ...>@: a call of a rule template (ADR 0031), with the
    -- value arguments of @Name<e, ...>(x, ...)@ (ADR 0055).
    ETemplate Loc Text [Expr] [Located Text]
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
-- for errors, given the path of the grammar and its @%import@s
-- ('grammarImports'). The file is the one of the location
-- ('diagnosticFile'): the grammar, written as given, or a library that it
-- imports (ADR 0092).
--
-- @
-- either (mapM_ (TIO.hPutStrLn stderr . renderDiagnostic \"Calc.hpeg\" [])) (const (pure ())) (parseGrammar src)
-- @
renderDiagnostic :: FilePath -> [Located FilePath] -> Diagnostic -> Text
renderDiagnostic file imports (Diagnostic (Loc f l c) msg) =
  T.concat [T.pack (diagnosticFile file imports f), ":", T.pack (show l), ":", T.pack (show c), ": error: ", msg]

-- | The path of the file of a location ('locFile'), given the path of the
-- grammar and its @%import@s: the grammar for @0@, and for @i@ the path of
-- the @i@-th import joined to the directory of the grammar
-- ('importedPath'). A number without an import is the grammar.
diagnosticFile :: FilePath -> [Located FilePath] -> Int -> FilePath
diagnosticFile file imports i = case drop (i - 1) imports of
  Located _ p : _ | i > 0 -> importedPath file p
  _ -> file

-- | The path of a library given the path of the grammar that imports it
-- and the path of its @%import@ (ADR 0092): the import joined with @/@ to
-- the directory of the grammar, or the import itself when the path of the
-- grammar has no directory.
--
-- @
-- importedPath \"grammar\/Calc.hpeg\" \"lex\/Ident.hpeg\" == \"grammar\/lex\/Ident.hpeg\"
-- importedPath \"Calc.hpeg\" \"lex\/Ident.hpeg\" == \"lex\/Ident.hpeg\"
-- @
importedPath :: FilePath -> FilePath -> FilePath
importedPath file p = case break (== '/') (reverse file) of
  (_, '/' : dir) -> reverse dir <> "/" <> p
  _ -> p

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

-- | The variables that a piece of Haskell code refers to, in order, with
-- their locations, given the location of the first character of the code
-- (ADR 0082). A variable is an identifier that does not start with an
-- upper case letter and is not a reserved word of Haskell; a name in
-- back quotes (@\`div\`@) counts. The reading is lexical, not a parse: a
-- variable bound inside the code (@\\x -> x@) counts too. It skips
--
-- * string literals (@"..."@, with escapes) and character literals
--   (@'a'@, @'\\n'@, @'\\''@); a quote inside an identifier (@x'@) is part
--   of it,
-- * line comments (@--@ to the end of the line, but not an operator such
--   as @-->@) and nested block comments (@{- ... -}@),
-- * qualified names (@M.x@, @Data.Map.lookup@), whose qualifier starts
--   with an upper case letter,
-- * the fields of a record field selection (@r.x@, with no space before
--   the dot); the record is a variable.
--
-- Template Haskell quotations are read as code.
--
-- @
-- codeVariables (Loc 0 3 8) " y > 0 " == [Located (Loc 0 3 9) "y"]
-- @
codeVariables :: Loc -> Text -> [Located Text]
codeVariables start code = go (zip (scanl advance start chars) chars)
  where
    chars = T.unpack code
    advance (Loc f ln col) c
      | c == '\n' = Loc f (ln + 1) 1
      | otherwise = Loc f ln (col + 1)
    -- The characters that remain, each with its location.
    go [] = []
    go s@((l, c) : rest)
      | c == '"' = go (string rest)
      | c == '\'' = maybe (go rest) go (charLiteral rest)
      | c == '-', (dashes, after) <- span ((== '-') . snd) s, length dashes >= 2, not (startsSymbol after) = go (dropWhile ((/= '\n') . snd) after)
      | c == '{', (_, '-') : after <- rest = go (blockComment (1 :: Int) after)
      | isDigit c = go (dropWhile (isIdentChar . snd) rest)
      | isIdentStart c =
          let (name, after) = identifier s
           in case after of
                (_, '.') : after'@((_, d) : _)
                  | isUpper c, isIdentStart d -> go (qualified after')
                  | isUpper c, isSymbolChar d -> go (dropWhile (isSymbolChar . snd) after')
                  | not (isUpper c), isIdentStart d, not (isUpper d) -> variable l c name ++ go (fields after')
                _ -> variable l c name ++ go after
      | otherwise = go rest
    identifier s = let (xs, after) = span (isIdentChar . snd) s in (T.pack (map snd xs), after)
    variable l c name
      | isUpper c || name `elem` reservedWords = []
      | otherwise = [Located l name]
    isIdentStart c = isAlpha c || c == '_'
    isIdentChar c = isAlphaNum c || c == '_' || c == '\''
    isSymbolChar c = c `elem` ("!#$%&*+./<=>?@\\^|-~:" :: String) || (c > '\x7f' && (isSymbol c || isPunctuation c))
    startsSymbol s = case s of
      (_, c) : _ -> isSymbolChar c
      [] -> False
    -- The rest after the closing quote of a string literal.
    string s = case s of
      [] -> []
      (_, '\\') : _ : r -> string r
      (_, '"') : r -> r
      _ : r -> string r
    -- The rest after a character literal that starts after the quote, or
    -- Nothing when the quote does not start one (a promoted constructor or
    -- a quoted name of Template Haskell).
    charLiteral s = case s of
      (_, '\\') : _ : r -> Just (drop 1 (dropWhile ((/= '\'') . snd) r))
      (_, c) : (_, '\'') : r | c /= '\n' -> Just r
      _ -> Nothing
    -- The rest after a block comment, given the depth of nesting.
    blockComment depth s = case s of
      [] -> []
      (_, '-') : (_, '}') : r -> if depth == 1 then r else blockComment (depth - 1) r
      (_, '{') : (_, '-') : r -> blockComment (depth + 1) r
      _ : r -> blockComment depth r
    -- The rest after the names and dots of a qualified name whose first
    -- qualifier has been read, starting at the next name: M.x, M.N.x, M.+
    qualified s@((_, c) : _) =
      let (_, after) = identifier s
       in case after of
            (_, '.') : after'@((_, d) : _)
              | isUpper c, isIdentStart d -> qualified after'
              | isUpper c, isSymbolChar d -> dropWhile (isSymbolChar . snd) after'
            _ -> after
    qualified [] = []
    -- The rest after the fields of a selection, starting at a field.
    fields s =
      let (_, after) = identifier s
       in case after of
            (_, '.') : after'@((_, d) : _) | isIdentStart d, not (isUpper d) -> fields after'
            _ -> after

-- | The reserved words of Haskell 2010, which are not variables.
reservedWords :: [Text]
reservedWords =
  [ "case", "class", "data", "default", "deriving", "do", "else", "forall", "foreign", "if", "import", "in"
  , "infix", "infixl", "infixr", "instance", "let", "module", "newtype", "of", "then", "type", "where", "_"
  ]
