{-# LANGUAGE OverloadedStrings #-}

-- | Generate a Haskell module from a grammar.
--
-- The generator is a pure function from a grammar to the text of a module
-- (ADR 0002); 'generateFromSource' and 'generate' are its entry points, and
-- @peg-hs gen@ calls them. The generated module depends only on the
-- @peg-runtime@ package. Its public interface is described in ADR 0014.
-- For a start rule @Expr@ of type @T@ it exports:
--
-- * @parse :: Text -> Either ParseError T@ for the start rule, and
--   @parseName@ for each rule @Name@ in @%entry@;
-- * with labels (ADR 0021), @parseRecover :: Text -> (Maybe T, [SyntaxError])@
--   and its @%entry@ variants;
-- * with @%syntax@ (ADR 0019), @parseSyntax@ and, with labels,
--   @parseSyntaxRecover@, which return a @SyntaxNode@, together with the
--   syntax kinds, typed wrappers and accessors described in
--   @Peg.Runtime.Syntax@;
-- * the names listed by @%export@.
--
-- 'optExports' narrows the first three kinds of names to those given, as
-- @peg-hs gen --export NAME@ does (ADR 0061). The names of @%export@ are
-- always exported. The module then has only the declarations that the
-- names exported refer to, so that it compiles without warnings under
-- @-Wall@: the rules that no exported entry point reaches, their fields in
-- the memo tables, and the syntax kinds, wrappers and accessors that are
-- not exported or used are left out.
--
-- With @%env@, every entry point first takes the environment. The types
-- @ParseError@ and @SyntaxError@ come from the @Peg.Runtime@ module of
-- @peg-runtime@, and @SyntaxNode@ from @Peg.Runtime.Syntax@.
--
-- The grammar is checked before generating (see 'generate'), but the
-- warnings about labels are not computed here; call
-- @Peg.Grammar.Labels.labelWarnings@ for them, as @peg-hs gen@ does.
module Peg.Codegen
  ( Options (..)
  , defaultOptions
  , generate
  , generateFromSource
  , runtimeVersions
  ) where

import Data.Char (toLower, toUpper)
import Data.List (intersperse)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust, isNothing)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Check
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)

-- | Options for generation.
data Options = Options
  { optSourceName :: FilePath
  -- ^ The grammar file name written into @LINE@ pragmas. Use the path as
  -- given on the command line, so that the output does not depend on the
  -- directory layout of the machine.
  , optOutputName :: FilePath
  -- ^ The name of the generated file, used to point @LINE@ pragmas back at
  -- the generated code after each fragment of user code.
  , optDebugEntry :: Bool
  -- ^ Also export @peg'parseWith@, which takes a runtime configuration and
  -- returns statistics, and its variants for the syntax tree and recovery
  -- (@peg'parseSyntaxWith@, @peg'parseRecoverWith@,
  -- @peg'parseSyntaxRecoverWith@) when the grammar has them. Only meant for
  -- testing the generator (@peg-hs gen --debug-entry@).
  , optExports :: Maybe [Text]
  -- ^ The names to export of those the generator defines: the entry points
  -- (@parse@, @parseName@, @parseSyntax@, @parseRecover@,
  -- @parseSyntaxRecover@ and their @%entry@ variants) and the names of
  -- @%syntax@ (@nameOfSyntaxKind@, @isTriviaSyntaxKind@, the syntax kinds,
  -- the wrapper types, named without @(..)@, their casts and accessors).
  -- The order and repetitions of the names do not matter. A name that the
  -- generator does not define is an error of 'generate'. The names of
  -- @%export@ and the debugging entry points of 'optDebugEntry' are always
  -- exported, and the code of the grammar is always generated: if it refers
  -- to a declaration that is left out, GHC reports the name as not in
  -- scope, and the name must be exported. 'Nothing', the default, exports
  -- every name (ADR 0061).
  }
  deriving (Eq, Show)

-- | Options for a grammar named @Grammar.hpeg@ generated into @Grammar.hs@,
-- without the debugging entry points, exporting every name. Override the file names with record
-- update syntax.
defaultOptions :: Options
defaultOptions = Options "Grammar.hpeg" "Grammar.hs" False Nothing

-- | Parse, check and generate: 'Peg.Grammar.Parser.parseGrammar' followed
-- by 'generate'. The diagnostics are errors, located in the grammar.
--
-- @
-- import qualified Data.Text.IO as TIO
-- import Peg.Codegen
-- import Peg.Grammar (renderDiagnostic)
--
-- main :: IO ()
-- main = do
--   src <- TIO.readFile \"grammar\/Calc.hpeg\"
--   let opts = defaultOptions {optSourceName = \"grammar\/Calc.hpeg\", optOutputName = \"src\/Calc.hs\"}
--   case generateFromSource opts src of
--     Left diags -> mapM_ (TIO.putStrLn . renderDiagnostic \"grammar\/Calc.hpeg\") diags
--     Right code -> TIO.writeFile \"src\/Calc.hs\" code
-- @
--
-- The name of the generated module is the one given by @%module@ in the
-- grammar; 'optOutputName' is only written into @LINE@ pragmas.
generateFromSource :: Options -> Text -> Either [Diagnostic] Text
generateFromSource opts src = parseGrammar src >>= generate opts

-- | Check a grammar and generate its module. Templates are expanded first
-- ('Peg.Grammar.Templates.expandTemplates', ADR 0031), then the grammar
-- is checked by 'Peg.Grammar.Check.check'; errors inside a template name
-- the call that expanded it ('Peg.Grammar.Templates.templateNotes'). The
-- grammar may be given before or after the expansion of templates.
--
-- With 'optExports', every name given must be one that the generator
-- defines for the grammar; each one that is not is an error at line 1,
-- column 1, in the order given:
-- @the generator does not define NAME@ (ADR 0061).
generate :: Options -> Grammar -> Either [Diagnostic] Text
generate opts g0 = do
  g <- either (Left . templateNotes g0) Right (expandTemplates g0)
  analysis <- either (Left . templateNotes g0) Right (check g)
  case undefinedExports opts g analysis of
    [] -> Right (finalize opts (render opts g analysis))
    missing -> Left [Diagnostic (Loc 1 1) ("the generator does not define " <> n) | n <- missing]

-- Labels written anywhere in the grammar (ADR 0021).
grammarLabels :: Grammar -> [Text]
grammarLabels g = [name | r <- grammarRules g, a <- ruleAlts r, name <- concatMap (exprLabels . itemExpr) (altItems a)]

-- Fragments of user code ----------------------------------------------------

restoreMarker :: Text
restoreMarker = "{-# PEG'RESTORE #-}"

-- Place a fragment of user code so that GHC reports its errors at the
-- fragment's line and column in the grammar file. The pragmas must not
-- start a line that the layout rule would see, so COLUMN shares the line
-- with the fragment and the code after it is indented.
fragment :: Options -> Located Text -> Text
fragment opts (Located (Loc l c) t) =
  T.concat
    [ "\n{-# LINE "
    , showT l
    , " "
    , T.pack (show (optSourceName opts))
    , " #-}\n {-# COLUMN "
    , showT c
    , " #-}"
    , t
    , "\n"
    , restoreMarker
    , "\n    "
    ]

-- Replace each restore marker by a LINE pragma that points at the next line
-- of the generated file.
finalize :: Options -> Text -> Text
finalize opts t = T.unlines (zipWith fix [1 :: Int ..] (T.lines t))
  where
    fix n line
      | line == restoreMarker = "{-# LINE " <> showT (n + 1) <> " " <> T.pack (show (optOutputName opts)) <> " #-}"
      | otherwise = line

showT :: Show a => a -> Text
showT = T.pack . show

hsString :: Text -> Text
hsString = T.pack . show . T.unpack

-- Module ------------------------------------------------------------------------

data Env = Env
  { envOpts :: Options
  , envGrammar :: Grammar
  , envAnalysis :: Analysis
  , envRules :: M.Map Text Rule
  , envSyntax :: Bool
  -- ^ @%syntax@: every parser also returns syntax tree children (ADR 0019).
  }

-- | The versions of peg-runtime that generated modules need, as a range of
-- Cabal, which the header of every generated module names (ADR 0046).
-- Generated modules use "Peg.Runtime.Internal", whose changes are major
-- changes of peg-runtime under the PVP: the range goes up when the
-- generator needs such a change.
runtimeVersions :: Text
runtimeVersions = "peg-runtime >=0.1 && <0.2"

render :: Options -> Grammar -> Analysis -> Text
render opts g an =
  T.intercalate
    "\n"
    ( [ "-- This module was generated by peg-hs from " <> T.pack (optSourceName opts) <> ". Do not edit it by hand."
      , "-- It needs " <> runtimeVersions <> "."
      ]
        ++ ["{-# LANGUAGE " <> unLoc x <> " #-}" | x <- grammarLanguages g]
        ++ ["{-# OPTIONS_GHC -Wno-unused-imports -Wno-unused-top-binds #-}" | pruned]
        ++ [ "module " <> unLoc (grammarModule g)
      , "  ( " <> T.intercalate "\n  , " exports
      , "  ) where"
      , ""
      ]
        ++ ["import qualified Prelude as PegPrelude" | usesPegPrelude]
        ++ [ "import qualified Peg.Runtime.Internal as PegRt"
           ]
        ++ ["import Prelude" | not (importsPrelude g)]
        ++ [""]
        ++ map verbatimBlock (grammarVerbatim g)
        ++ decls
    )
  where
    env = Env opts g an (M.fromList [(ruleName r, r) | r <- grammarRules g]) syntax
    syntax = isJust (grammarSyntax g)
    start = analysisStart an
    entries = entryPoints g an
    -- The declarations that are generated (ADR 0061): all of them without
    -- 'optExports'.
    kept = keptDecls opts g an
    keep name = maybe True (S.member name) kept
    -- Declarations are left out: the code of the grammar that only their
    -- actions used, and the import of Prelude for that code, may then be
    -- unused, and the generator, which does not read Haskell, cannot tell
    -- (ADR 0062).
    pruned = case kept of
      Nothing -> False
      Just names -> Just names /= keptDecls opts {optExports = Just (map selectable (generatedNames g an))} g an
    decls =
      entryDecls
        ++ syntaxEntryDecls
        ++ recoverEntryDecls
        ++ debugDecls
        ++ syntaxDecls env keep
        ++ (if keep "peg'config" then [configDecl] else [])
        ++ (if keep "peg'newStore" then [storeDecl, newStoreDecl] else [])
        ++ [ruleDecl env r | r <- grammarRules g, keep (ruleVar (ruleName r))]
    -- Without the entry points and rules, the declarations may not use the
    -- qualified Prelude, whose import would then be redundant.
    usesPegPrelude = isNothing kept || any ("PegPrelude." `T.isInfixOf`) decls
    exports =
      [x | x <- generatedNames g an, maybe True (elem (selectable x)) (optExports opts)]
        ++ map unLoc (grammarExports g)
        ++ debugNames opts g
    recovering = isRecovering g
    -- In syntax mode a rule returns its value with its tree children.
    valueOf = if syntax then "PegPrelude.fmap PegPrelude.fst " else ""
    wrapValue e = if syntax then valueOf <> "(" <> e <> ")" else e
    hasEnv = isJust (grammarEnv g)
    -- When the generator restores the implicit Prelude import, it also uses
    -- it, so that the import is never reported as redundant.
    fstName = if importsPrelude g then "PegPrelude.fst" else "Prelude.fst"
    envType = maybe "()" (fragment opts) (grammarEnv g)
    resultType n = maybe "()" (fragment opts . ruleType) (M.lookup n (envRules env))
    verbatimBlock (Located (Loc l _) t) =
      T.concat ["{-# LINE ", showT l, " ", T.pack (show (optSourceName opts)), " #-}\n", t, "\n", restoreMarker, "\n"]
    envArg = if hasEnv then " peg'env" else ""
    envParamType = if hasEnv then "(" <> envType <> ") -> " else ""
    entryDecls =
      concat
        [ [ "-- | Parse the whole input with the rule @" <> n <> "@."
          , entryName k <> " :: " <> envParamType <> "PegRt.Text -> PegPrelude.Either PegRt.ParseError (" <> resultType n <> ")"
          , entryName k <> envArg <> " peg'input ="
          , "  " <> wrapValue (fstName <> " (PegRt.runParser peg'config (peg'newStore" <> envArg <> ") " <> ruleVar n <> " peg'input)")
          , ""
          ]
        | (k, n) <- entries
        , keep (entryName k)
        ]
    syntaxEntryDecls
      | syntax =
          concat
            [ [ "-- | Parse the whole input with the rule @" <> n <> "@ and return its lossless syntax tree."
              , "parseSyntax" <> maybe "" id k <> " :: " <> envParamType <> "PegRt.Text -> PegPrelude.Either PegRt.ParseError PegRt.SyntaxNode"
              , "parseSyntax" <> maybe "" id k <> envArg <> " peg'input ="
              , "  PegPrelude.fmap (\\peg'r -> PegRt.syntaxRoot peg'input " <> kindVar n <> " (PegPrelude.snd peg'r)) (" <> fstName <> " (PegRt.runParser peg'config (peg'newStore" <> envArg <> ") " <> ruleVar n <> " peg'input))"
              , ""
              ]
            | (k, n) <- entries
            , keep ("parseSyntax" <> maybe "" id k)
            ]
      | otherwise = []
    recoverEntryDecls
      | recovering =
          concat
            [ ( if keep ("parseRecover" <> maybe "" id k)
                  then
                    [ "-- | Parse the whole input with the rule @" <> n <> "@, recovering from labelled failures."
                    , "-- The value is 'PegPrelude.Nothing' only if the rule could not be recovered."
                    , "parseRecover" <> maybe "" id k <> " :: " <> envParamType <> "PegRt.Text -> (PegPrelude.Maybe (" <> resultType n <> "), [PegRt.SyntaxError])"
                    , "parseRecover" <> maybe "" id k <> envArg <> " peg'input ="
                    , "  let (peg'v, peg'e, _) = PegRt.runParserRecover peg'config (peg'newStore" <> envArg <> ") " <> ruleVar n <> " peg'input"
                    , "   in (" <> valueOf <> "peg'v, peg'e)"
                    , ""
                    ]
                  else []
              )
                ++ ( if syntax && keep ("parseSyntaxRecover" <> maybe "" id k)
                       then
                         [ "-- | The lossless syntax tree of the whole input, recovering from labelled failures."
                         , "-- Always returns a tree; unrecovered input becomes error nodes."
                         , "parseSyntaxRecover" <> maybe "" id k <> " :: " <> envParamType <> "PegRt.Text -> (PegRt.SyntaxNode, [PegRt.SyntaxError])"
                         , "parseSyntaxRecover" <> maybe "" id k <> envArg <> " peg'input ="
                         , "  let (peg'n, peg'e, _) = PegRt.runSyntaxRecover peg'config (peg'newStore" <> envArg <> ") " <> ruleVar n <> " " <> kindVar n <> " peg'input"
                         , "   in (peg'n, peg'e)"
                         , ""
                         ]
                       else []
                   )
            | (k, n) <- entries
            ]
            ++ ( if optDebugEntry opts
                   then
                     [ "-- | Like 'peg'parseWith', recovering. Only meant for testing the generator."
                     , "peg'parseRecoverWith :: PegRt.Config -> " <> envParamType <> "PegRt.Text -> (PegPrelude.Maybe (" <> resultType start <> "), [PegRt.SyntaxError], PegRt.Stats)"
                     , "peg'parseRecoverWith peg'cfg" <> envArg <> " peg'input ="
                     , "  let (peg'v, peg'e, peg's) = PegRt.runParserRecover peg'cfg {PegRt.cfgTabstop = PegRt.cfgTabstop peg'config} (peg'newStore" <> envArg <> ") " <> ruleVar start <> " peg'input"
                     , "   in (" <> valueOf <> "peg'v, peg'e, peg's)"
                     , ""
                     ]
                       ++ ( if syntax
                              then
                                [ "-- | Like 'peg'parseSyntaxWith', recovering. Only meant for testing the generator."
                                , "peg'parseSyntaxRecoverWith :: PegRt.Config -> " <> envParamType <> "PegRt.Text -> (PegRt.SyntaxNode, [PegRt.SyntaxError], PegRt.Stats)"
                                , "peg'parseSyntaxRecoverWith peg'cfg" <> envArg <> " peg'input ="
                                , "  PegRt.runSyntaxRecover peg'cfg {PegRt.cfgTabstop = PegRt.cfgTabstop peg'config} (peg'newStore" <> envArg <> ") " <> ruleVar start <> " " <> kindVar start <> " peg'input"
                                , ""
                                ]
                              else []
                          )
                   else []
               )
      | otherwise = []
    debugDecls
      | optDebugEntry opts =
          [ "-- | Run the start rule with a runtime configuration and return statistics."
          , "-- Only meant for testing the generator."
          , "peg'parseWith :: PegRt.Config -> " <> envParamType <> "PegRt.Text -> (PegPrelude.Either PegRt.ParseError (" <> resultType start <> "), PegRt.Stats)"
          , "peg'parseWith peg'cfg" <> envArg <> " peg'input ="
          ]
            ++ ( if syntax
                   then
                     [ "  let (peg'r, peg's) = PegRt.runParser peg'cfg {PegRt.cfgTabstop = PegRt.cfgTabstop peg'config} (peg'newStore" <> envArg <> ") " <> ruleVar start <> " peg'input"
                     , "   in (" <> valueOf <> "peg'r, peg's)"
                     ]
                   else ["  PegRt.runParser peg'cfg {PegRt.cfgTabstop = PegRt.cfgTabstop peg'config} (peg'newStore" <> envArg <> ") " <> ruleVar start <> " peg'input"]
               )
            ++ [""]
            ++ ( if syntax
                   then
                     [ "-- | Like 'peg'parseWith', for the syntax tree. Only meant for testing the generator."
                     , "peg'parseSyntaxWith :: PegRt.Config -> " <> envParamType <> "PegRt.Text -> (PegPrelude.Either PegRt.ParseError PegRt.SyntaxNode, PegRt.Stats)"
                     , "peg'parseSyntaxWith peg'cfg" <> envArg <> " peg'input ="
                     , "  let (peg'r, peg's) = PegRt.runParser peg'cfg {PegRt.cfgTabstop = PegRt.cfgTabstop peg'config} (peg'newStore" <> envArg <> ") " <> ruleVar start <> " peg'input"
                     , "   in (PegPrelude.fmap (\\peg'x -> PegRt.syntaxRoot peg'input " <> kindVar start <> " (PegPrelude.snd peg'x)) peg'r, peg's)"
                     , ""
                     ]
                   else []
               )
      | otherwise = []
    configDecl =
      T.intercalate
        "\n"
        [ "peg'config :: PegRt.Config"
        , "peg'config = PegRt.defaultConfig" <> maybe "" (\t -> " {PegRt.cfgTabstop = " <> showT (unLoc t) <> "}") (grammarTabstop g)
        , ""
        ]
    memoised = [r | r <- grammarRules g, not (isNoMemo g r), keep (ruleVar (ruleName r))]
    storeFields =
      ["peg'env :: (" <> envType <> ")" | hasEnv]
        ++ [memoVar r <> " :: " <> tableType r | r <- memoised]
    tableType r = case ruleParams r of
      [] -> "PegRt.Table peg's " <> resultTypeText env r
      ps -> "PegRt.ArgTable peg's (" <> keyType ps <> ") " <> resultTypeText env r
    keyType [p] = fragment opts (paramType p)
    keyType ps = T.intercalate ", " ["(" <> fragment opts (paramType p) <> ")" | p <- ps]
    storeDecl
      | null storeFields = "data Peg'Store peg's = Peg'Store\n"
      | otherwise =
          T.intercalate
            "\n"
            [ "data Peg'Store peg's = Peg'Store"
            , "  { " <> T.intercalate "\n  , " storeFields
            , "  }"
            , ""
            ]
    newStoreDecl =
      T.intercalate
        "\n"
        [ "peg'newStore :: " <> envParamType <> "PegRt.ST peg's (Peg'Store peg's)"
        , "peg'newStore" <> envArg <> " ="
        , if null memoised
            then "  PegPrelude.pure (Peg'Store" <> envArg <> ")"
            else
              "  Peg'Store" <> envArg
                <> T.concat (zipWith (<>) (" PegPrelude.<$> " : repeat " PegPrelude.<*> ") [newTable r | r <- memoised])
        , ""
        ]
    newTable r = if null (ruleParams r) then "PegRt.newTable" else "PegRt.newArgTable"

-- Selecting the exports (ADR 0061) -------------------------------------------

-- The entry points: the start rule, then the rules of @%entry@.
entryPoints :: Grammar -> Analysis -> [(Maybe Text, Text)]
entryPoints g an = (Nothing, analysisStart an) : [(Just (unLoc e), unLoc e) | e <- grammarEntries g]

entryName :: Maybe Text -> Text
entryName = ("parse" <>) . maybe "" id

isRecovering :: Grammar -> Bool
isRecovering = not . null . grammarLabels

-- The public names that the generator defines, as the export list writes
-- them, in its order: the entry points, then the names of @%syntax@.
generatedNames :: Grammar -> Analysis -> [Text]
generatedNames g an =
  [entryName k | (k, _) <- entries]
    ++ ["parseSyntax" <> maybe "" id k | syntax, (k, _) <- entries]
    ++ ["parseRecover" <> maybe "" id k | recovering, (k, _) <- entries]
    ++ ["parseSyntaxRecover" <> maybe "" id k | recovering, syntax, (k, _) <- entries]
    ++ syntaxExports g
  where
    entries = entryPoints g an
    syntax = isJust (grammarSyntax g)
    recovering = isRecovering g

-- The entry points of @--debug-entry@, which are always exported with it.
debugNames :: Options -> Grammar -> [Text]
debugNames opts g =
  ["peg'parseWith" | optDebugEntry opts]
    ++ ["peg'parseSyntaxWith" | optDebugEntry opts, syntax]
    ++ ["peg'parseRecoverWith" | optDebugEntry opts, recovering]
    ++ ["peg'parseSyntaxRecoverWith" | optDebugEntry opts, recovering, syntax]
  where
    syntax = isJust (grammarSyntax g)
    recovering = isRecovering g

-- The name by which a public name is selected: a type without @(..)@.
selectable :: Text -> Text
selectable x = maybe x id (T.stripSuffix "(..)" x)

-- The names of 'optExports' that the generator does not define, each once,
-- in the order given.
undefinedExports :: Options -> Grammar -> Analysis -> [Text]
undefinedExports opts g an = case optExports opts of
  Nothing -> []
  Just names -> nubOrd [n | n <- names, not (S.member n defined)]
  where
    defined = S.fromList (map selectable (generatedNames g an))
    nubOrd = go S.empty
    go _ [] = []
    go seen (x : xs)
      | S.member x seen = go seen xs
      | otherwise = x : go (S.insert x seen) xs

-- The declarations to generate with 'optExports': those reachable from the
-- selected names and the debugging entry points, by the references of the
-- generated code. 'Nothing' without 'optExports': every declaration. A
-- declaration is named by its Haskell name; @Peg'Store@ goes with
-- @peg'newStore@, and a field of the store with its rule.
keptDecls :: Options -> Grammar -> Analysis -> Maybe (Set Text)
keptDecls opts g an = case optExports opts of
  Nothing -> Nothing
  Just names ->
    let selected = S.fromList names
        roots = [x | x <- map selectable (generatedNames g an), S.member x selected] ++ debugNames opts g
     in Just (reach S.empty roots)
  where
    reach seen [] = seen
    reach seen (x : xs)
      | S.member x seen = reach seen xs
      | otherwise = reach (S.insert x seen) (M.findWithDefault [] x refs ++ xs)
    syntax = isJust (grammarSyntax g)
    start = analysisStart an
    runner n withKind = [ruleVar n, "peg'config", "peg'newStore"] ++ [kindVar n | withKind]
    refs =
      M.fromList $
        concat
          [ [ (entryName k, runner n False)
            , ("parseSyntax" <> maybe "" id k, runner n True)
            , ("parseRecover" <> maybe "" id k, runner n False)
            , ("parseSyntaxRecover" <> maybe "" id k, runner n True)
            ]
          | (k, n) <- entryPoints g an
          ]
          ++ [ ("peg'parseWith", runner start False)
             , ("peg'parseSyntaxWith", runner start True)
             , ("peg'parseRecoverWith", runner start False)
             , ("peg'parseSyntaxRecoverWith", runner start True)
             ]
          ++ [(ruleVar (ruleName r), ruleRefs r) | r <- grammarRules g]
          ++ [("isTriviaSyntaxKind", [kindVar (unLoc t) | t <- grammarTrivia g])]
          ++ concat
            [ (castName n, [syntaxTypeName n, kindVar n])
                : [(accessorName n b, syntaxTypeName n : accessRefs a) | (b, a) <- accessors g r]
            | r <- nodeRules g
            , let n = ruleName r
            ]
    ruleRefs r =
      [ruleVar m | alt <- ruleAlts r, i <- altItems alt, m <- exprRefs (itemExpr i)]
        ++ [ruleVar rec | alt <- ruleAlts r, i <- altItems alt, l <- exprLabels (itemExpr i), rec : _ <- [[unLoc x | (Located _ l', x) <- grammarRecovers g, l' == l]]]
        ++ [kindVar (ruleName r) | syntax, not (isInline g (ruleName r))]
    accessRefs a = case a of
      OneNode x -> [syntaxTypeName x, kindVar x]
      ManyNodes x -> [syntaxTypeName x, kindVar x]
      OneToken x -> [kindVar x]
      ManyTokens x -> [kindVar x]
      Elements -> ["isTriviaSyntaxKind"]

-- The rules that an expression refers to.
exprRefs :: Expr -> [Text]
exprRefs e = case e of
  ERef _ n _ -> [n]
  EGroup alts -> concatMap (concatMap (exprRefs . itemExpr)) alts
  EStar x -> exprRefs x
  EPlus x -> exprRefs x
  EOpt x -> exprRefs x
  EAnd x -> exprRefs x
  ENot x -> exprRefs x
  ECapture x -> exprRefs x
  ELabel _ x _ -> exprRefs x
  EDiscard x -> exprRefs x
  _ -> []

-- The labels written in an expression.
exprLabels :: Expr -> [Text]
exprLabels e = case e of
  ELabel _ x name -> name : exprLabels x
  EGroup alts -> concatMap (concatMap (exprLabels . itemExpr)) alts
  EStar x -> exprLabels x
  EPlus x -> exprLabels x
  EOpt x -> exprLabels x
  EAnd x -> exprLabels x
  ENot x -> exprLabels x
  ECapture x -> exprLabels x
  EDiscard x -> exprLabels x
  _ -> []

-- The generated code imports Prelude qualified, which turns off the implicit
-- import of Prelude for the user's code. Restore it unless the user's code
-- imports Prelude itself, as GHC would.
importsPrelude :: Grammar -> Bool
importsPrelude g =
  any isPreludeImport (concatMap (T.lines . unLoc) (grammarVerbatim g))
    || "NoImplicitPrelude" `elem` map unLoc (grammarLanguages g)
  where
    isPreludeImport line = case T.words line of
      "import" : rest -> "Prelude" `elem` take 2 rest
      _ -> False

isNoMemo :: Grammar -> Rule -> Bool
isNoMemo g r = ruleName r `elem` map unLoc (grammarNoMemo g)

ruleVar :: Text -> Text
ruleVar n = "peg'rule'" <> n

memoVar :: Rule -> Text
memoVar r = "peg'memo'" <> ruleName r

-- Rules -----------------------------------------------------------------------

-- The type of a rule's result: its value, and in syntax mode also its tree
-- children.
resultTypeText :: Env -> Rule -> Text
resultTypeText env r
  | envSyntax env = "((" <> ty <> "), [PegRt.Child])"
  | otherwise = "(" <> ty <> ")"
  where
    ty = fragment (envOpts env) (ruleType r)

ruleDecl :: Env -> Rule -> Text
ruleDecl env r =
  T.intercalate
    "\n"
    [ ruleVar (ruleName r) <> " :: " <> T.concat ["(" <> fragment opts (paramType p) <> ") -> " | p <- ruleParams r]
        <> "PegRt.P (Peg'Store peg's) peg's "
        <> resultTypeText env r
    , ruleVar (ruleName r) <> T.concat [" " <> paramName p | p <- ruleParams r] <> " ="
    , "  " <> memoCall <> "\n    (" <> treeWrap <> "PegRt.choice\n      [ " <> T.intercalate "\n      , " alts <> "\n      ])" <> treeClose
    , ""
    ]
  where
    opts = envOpts env
    name = ruleName r
    lr = S.member name (analysisLeftRecursive (envAnalysis env))
    memoCall = case ruleParams r of
      _ | isNoMemo (envGrammar env) r -> "PegRt.nomemo " <> hsString name
      []
        | lr -> "PegRt.memoLR " <> memoVar r <> " " <> hsString name
        | otherwise -> "PegRt.memo " <> memoVar r <> " " <> hsString name
      [p] -> "PegRt.memoArg " <> memoVar r <> " " <> hsString name <> " " <> paramName p
      ps -> "PegRt.memoArg " <> memoVar r <> " " <> hsString name <> " (" <> T.intercalate ", " (map paramName ps) <> ")"
    alts
      | envSyntax env = fst (runGen (mapM (altCodeS env) (ruleAlts r)) 0)
      | otherwise = fst (runGen (mapM (altCode env) (ruleAlts r)) 0)
    g = envGrammar env
    (treeWrap, treeClose)
      | not (envSyntax env) = ("", "")
      | isInline g name = ("", "")
      | isToken g name = ("PegRt.token " <> kindVar name <> " (", ")")
      | otherwise = ("PegRt.node " <> kindVar name <> " (", ")")

-- A counter for fresh variable names.
newtype Gen a = Gen {runGen :: Int -> (a, Int)}

instance Functor Gen where
  fmap f (Gen g) = Gen $ \n -> let (a, n') = g n in (f a, n')

instance Applicative Gen where
  pure x = Gen $ \n -> (x, n)
  Gen f <*> Gen x = Gen $ \n -> let (f', n') = f n; (x', n'') = x n' in (f' x', n'')

instance Monad Gen where
  Gen g >>= k = Gen $ \n -> let (a, n') = g n in runGen (k a) n'

fresh :: Gen Text
fresh = Gen $ \n -> ("peg'v" <> showT n, n + 1)

doBlock :: [Text] -> Text
doBlock stmts = "do { " <> T.concat (intersperse "\n          ; " stmts) <> "\n          }"

altCode :: Env -> Alt -> Gen Text
altCode env a = do
  let envStmt = ["_env <- PegRt.askStore peg'env" | isJust (grammarEnv (envGrammar env))]
      items = altItems a
  case altAction a of
    Just act -> do
      stmts <- mapM (itemStmt env True) items
      pure $
        doBlock
          ( envStmt
              ++ ["peg'start <- PegRt.getOffset"]
              ++ stmts
              ++ ["_span <- PegRt.spanFrom peg'start", "PegPrelude.pure (" <> fragment (envOpts env) act <> ")"]
          )
    Nothing -> do
      (stmts, result) <- passThrough env True items
      pure (doBlock (envStmt ++ stmts ++ ["PegPrelude.pure " <> result]))

-- The item whose value a sequence without an action returns (ADR 0030).
passedItem :: Env -> [Item] -> Maybe Item
passedItem env items = case countedItems (units env) items of
  [i] -> Just i
  _ -> Nothing

units :: Env -> Set Text
units = analysisUnit . envAnalysis

-- Statements for a sequence whose single value is returned unchanged.
passThrough :: Env -> Bool -> [Item] -> Gen ([Text], Text)
passThrough env honorBind items = go items
  where
    chosen = passedItem env items
    go [] = pure ([], "()")
    go (i : is)
      | Just i == chosen = do
          e <- exprCode env (itemExpr i)
          v <- case itemBind i of
            Just n | honorBind -> pure n
            _ -> fresh
          rest <- mapM (itemStmt env honorBind) is
          pure ((v <> " <- " <> e) : rest, v)
      | otherwise = do
          s <- itemStmt env honorBind i
          (rest, v) <- go is
          pure (s : rest, v)

itemStmt :: Env -> Bool -> Item -> Gen Text
itemStmt env honorBind i = do
  e <- exprCodeU env (valueUsed env honorBind i) (itemExpr i)
  pure $
    if hasValue (units env) (itemExpr i)
      then case itemBind i of
        Just n | honorBind -> n <> " <- " <> e
        _ -> "_ <- " <> e
      else e

-- Whether the value of an item in a sequence is used: only a bound item's
-- is, when bindings are honoured (ADR 0026).
valueUsed :: Env -> Bool -> Item -> Bool
valueUsed env honorBind i = honorBind && hasValue (units env) (itemExpr i) && isJust (itemBind i)

exprCode :: Env -> Expr -> Gen Text
exprCode env = exprCodeU env True

-- Code for an expression whose value is used, or discarded. A discarded
-- group is generated as a group without a value, so that its alternatives
-- need not have values of the same type (ADR 0026).
exprCodeU :: Env -> Bool -> Expr -> Gen Text
exprCodeU env used expr = case expr of
  ELit t orig -> pure ("PegRt.lit " <> hsString t <> " " <> hsString orig)
  EClass ranges orig ->
    pure
      ( "PegRt.cls ["
          <> T.intercalate ", " ["(" <> showT a <> ", " <> showT b <> ")" | (a, b) <- ranges]
          <> "] "
          <> hsString orig
      )
  EAny -> pure "PegRt.anyChar"
  ERef _ n [] -> pure (ruleVar n)
  ERef _ n args ->
    pure ("PegRt.withCol (\\_col -> " <> ruleVar n <> T.concat [" (" <> fragment opts x <> ")" | x <- args] <> ")")
  EGroup alts
    | used && hasValue (units env) expr -> do
        bodies <- mapM (\is -> passThrough env False is >>= \(stmts, v) -> pure (doBlock (stmts ++ ["PegPrelude.pure " <> v]))) alts
        pure ("PegRt.choice [" <> T.intercalate ", " bodies <> "]")
    | otherwise -> do
        bodies <- mapM (\is -> mapM (itemStmt env False) is >>= \stmts -> pure (doBlock (stmts ++ ["PegPrelude.pure ()"]))) alts
        pure ("PegRt.choice [" <> T.intercalate ", " bodies <> "]")
  EStar x -> wrap (if valued x then "PegRt.many" else "PegRt.skipMany") used x
  EPlus x -> wrap (if valued x then "PegRt.many1" else "PegRt.skipMany1") used x
  EOpt x -> wrap (if valued x then "PegRt.optional" else "PegRt.skipOptional") used x
  EAnd x -> wrap "PegRt.andP" False x
  ENot x -> wrap "PegRt.notP" False x
  ECapture x -> wrap "PegRt.capture" False x
  ELabel _ x name -> do
    e <- exprCodeU env used x
    pure ("PegRt.labeled " <> hsString name <> " " <> recoveryCode env False (valued x) name <> " (" <> e <> ")")
  EPred True f -> pure ("PegRt.predicate (\\_col -> " <> fragment opts f <> ")")
  EPred False f -> pure ("PegRt.predicate (\\_col -> PegPrelude.not (" <> fragment opts f <> "))")
  EDiscard x -> wrap "PegRt.voidP" False x
  ETemplate {} -> error "a template call must be expanded before generating code: call Peg.Grammar.Templates.expandTemplates first"
  where
    opts = envOpts env
    valued x = used && hasValue (units env) x
    wrap f inner x = do
      e <- exprCodeU env inner x
      pure (f <> " (" <> e <> ")")

-- Syntax trees (ADR 0019) ------------------------------------------------------

isToken :: Grammar -> Text -> Bool
isToken g n = n `elem` map unLoc (grammarTokens g)

isInline :: Grammar -> Text -> Bool
isInline g n = n `elem` map unLoc (grammarInline g)

-- Rules that appear in the tree as nodes and have a typed wrapper.
nodeRules :: Grammar -> [Rule]
nodeRules g = [r | r <- grammarRules g, not (isToken g (ruleName r)), not (isInline g (ruleName r))]

upperFirst :: Text -> Text
upperFirst t = case T.uncons t of
  Just (c, rest) -> T.cons (toUpper c) rest
  Nothing -> t

lowerFirst :: Text -> Text
lowerFirst t = case T.uncons t of
  Just (c, rest) -> T.cons (toLower c) rest
  Nothing -> t

kindVar :: Text -> Text
kindVar n = "syntaxKind" <> upperFirst n

castName :: Text -> Text
castName n = "cast" <> syntaxTypeName n

accessorName :: Text -> Text -> Text
accessorName rule binding = lowerFirst rule <> upperFirst binding

-- Kinds 0 and 1 are the text and error kinds of the runtime.
kindNumbers :: Grammar -> [(Text, Int)]
kindNumbers g = zip [ruleName r | r <- grammarRules g, not (isInline g (ruleName r))] [2 ..]

-- What an accessor returns.
data Access = OneNode Text | ManyNodes Text | OneToken Text | ManyTokens Text | Elements
  deriving (Eq)

accessors :: Grammar -> Rule -> [(Text, Access)]
accessors g r =
  [ (b, if all (== a) rest then a else Elements)
  | (b, a : rest) <- M.toList (M.fromListWith (flip (++)) [(b, [classify (itemExpr i)]) | alt <- ruleAlts r, i <- altItems alt, Just b <- [itemBind i]])
  ]
  where
    classify e = case e of
      ERef _ n _ | isToken g n -> OneToken n
      ERef _ n _ | not (isInline g n) -> OneNode n
      EOpt x -> classify x
      EStar x -> many x
      EPlus x -> many x
      _ -> Elements
    many x = case x of
      ERef _ n _ | isToken g n -> ManyTokens n
      ERef _ n _ | not (isInline g n) -> ManyNodes n
      _ -> Elements

syntaxExports :: Grammar -> [Text]
syntaxExports g
  | not (isJust (grammarSyntax g)) = []
  | otherwise =
      ["nameOfSyntaxKind", "isTriviaSyntaxKind"]
        ++ [kindVar n | (n, _) <- kindNumbers g]
        ++ concat
          [ [syntaxTypeName (ruleName r) <> "(..)", castName (ruleName r)]
              ++ [accessorName (ruleName r) b | (b, _) <- accessors g r]
          | r <- nodeRules g
          ]

-- The declarations of @%syntax@ that 'keep' accepts.
syntaxDecls :: Env -> (Text -> Bool) -> [Text]
syntaxDecls env keep
  | not (envSyntax env) = []
  | otherwise =
      concat
        [ [ "-- | The syntax kind of @" <> n <> "@."
          , kindVar n <> " :: PegRt.SyntaxKind"
          , kindVar n <> " = PegRt.SyntaxKind " <> showT k
          , ""
          ]
        | (n, k) <- kinds
        , keep (kindVar n)
        ]
        ++ (if keep "nameOfSyntaxKind" then nameDecl else [])
        ++ (if keep "isTriviaSyntaxKind" then triviaDecl else [])
        ++ concatMap typed (nodeRules g)
  where
    g = envGrammar env
    kinds = kindNumbers g
    nameDecl =
           [ "-- | The name of a syntax kind."
           , "nameOfSyntaxKind :: PegRt.SyntaxKind -> PegRt.Text"
           , "nameOfSyntaxKind peg'k = PegRt.labelText (case peg'k of"
           , "  { PegRt.SyntaxKind 0 -> " <> hsString "TEXT"
           , "  ; PegRt.SyntaxKind 1 -> " <> hsString "ERROR"
           ]
        ++ ["  ; PegRt.SyntaxKind " <> showT k <> " -> " <> hsString n | (n, k) <- kinds]
        ++ [ "  ; _ -> " <> hsString "UNKNOWN"
           , "  })"
           , ""
           ]
    triviaDecl =
      [ "-- | Whether a syntax kind is trivia (@%trivia@)."
      , "isTriviaSyntaxKind :: PegRt.SyntaxKind -> PegPrelude.Bool"
      , "isTriviaSyntaxKind peg'k = PegPrelude.elem peg'k [" <> T.intercalate ", " [kindVar n | n <- map unLoc (grammarTrivia g)] <> "]"
      , ""
      ]
    typed r =
      let n = ruleName r
          ty = syntaxTypeName n
       in ( if keep ty
              then
                [ "-- | A node of the rule @" <> n <> "@."
                , "newtype " <> ty <> " = " <> ty <> " PegRt.SyntaxNode"
                , "  deriving (PegPrelude.Eq, PegPrelude.Show)"
                , ""
                ]
              else []
          )
            ++ ( if keep (castName n)
                   then
                     [ "-- | The node, if it is a node of the rule @" <> n <> "@."
                     , castName n <> " :: PegRt.SyntaxNode -> PegPrelude.Maybe " <> ty
                     , castName n <> " peg'n ="
                     , "  if PegRt.syntaxKind peg'n PegPrelude.== " <> kindVar n <> " then PegPrelude.Just (" <> ty <> " peg'n) else PegPrelude.Nothing"
                     , ""
                     ]
                   else []
               )
            ++ concat [accessorDecl n ty b a | (b, a) <- accessors g r, keep (accessorName n b)]
    accessorDecl n ty b a =
      let name = accessorName n b
          lbl = "(PegRt.labelText " <> hsString b <> ")"
          (resTy, body) = case a of
            OneNode x -> ("PegPrelude.Maybe " <> syntaxTypeName x, "PegPrelude.fmap " <> syntaxTypeName x <> " (PegRt.labeledNode " <> kindVar x <> " " <> lbl <> " peg'n)")
            ManyNodes x -> ("[" <> syntaxTypeName x <> "]", "PegPrelude.map " <> syntaxTypeName x <> " (PegRt.labeledNodes " <> kindVar x <> " " <> lbl <> " peg'n)")
            OneToken x -> ("PegPrelude.Maybe PegRt.SyntaxToken", "PegRt.labeledToken " <> kindVar x <> " " <> lbl <> " peg'n")
            ManyTokens x -> ("[PegRt.SyntaxToken]", "PegRt.labeledTokens " <> kindVar x <> " " <> lbl <> " peg'n")
            Elements -> ("[PegRt.SyntaxElement]", "PegRt.labeledElements isTriviaSyntaxKind " <> lbl <> " peg'n")
       in [ "-- | The children bound to @" <> b <> "@ in the rule @" <> n <> "@."
          , name <> " :: " <> ty <> " -> " <> resTy
          , name <> " (" <> ty <> " peg'n) = " <> body
          , ""
          ]

freshK :: Gen Text
freshK = Gen $ \n -> ("peg'k" <> showT n, n + 1)

doReturn :: [Text] -> Text -> [Text] -> Text
doReturn stmts value kids = doBlock (stmts ++ ["PegPrelude.pure (" <> value <> ", " <> kidsExpr kids <> ")"])

kidsExpr :: [Text] -> Text
kidsExpr [] = "[]"
kidsExpr [k] = k
kidsExpr ks = "PegPrelude.concat [" <> T.intercalate ", " ks <> "]"

altCodeS :: Env -> Alt -> Gen Text
altCodeS env a = do
  let envStmt = ["_env <- PegRt.askStore peg'env" | isJust (grammarEnv (envGrammar env))]
      items = altItems a
  case altAction a of
    Just act -> do
      rs <- mapM (itemStmtS env True) items
      pure $
        doReturn
          (envStmt ++ ["peg'start <- PegRt.getOffset"] ++ map fst rs ++ ["_span <- PegRt.spanFrom peg'start"])
          ("(" <> fragment (envOpts env) act <> ")")
          (map snd rs)
    Nothing -> do
      (stmts, value, kids) <- passThroughS env True items
      pure (doReturn (envStmt ++ stmts) value kids)

-- Statements for a sequence whose single value is returned unchanged.
passThroughS :: Env -> Bool -> [Item] -> Gen ([Text], Text, [Text])
passThroughS env honorBind items = go items
  where
    chosen = passedItem env items
    go [] = pure ([], "()", [])
    go (i : is)
      | Just i == chosen = do
          e <- exprCodeS env (itemExpr i)
          k <- freshK
          (v, stmt) <- case itemBind i of
            Just n | honorBind -> pure (n, "(" <> n <> ", " <> k <> ") <- PegRt.label " <> hsString n <> " (" <> e <> ")\n          ; PegRt.touch " <> n)
            _ -> fresh >>= \v -> pure (v, "(" <> v <> ", " <> k <> ") <- " <> e)
          rest <- mapM (itemStmtS env honorBind) is
          pure (stmt : map fst rest, v, k : map snd rest)
      | otherwise = do
          (s, k) <- itemStmtS env honorBind i
          (rest, v, ks) <- go is
          pure (s : rest, v, k : ks)

itemStmtS :: Env -> Bool -> Item -> Gen (Text, Text)
itemStmtS env honorBind i = do
  e <- exprCodeSU env (valueUsed env honorBind i) (itemExpr i)
  k <- freshK
  pure $ case itemBind i of
    Just n | honorBind && hasValue (units env) (itemExpr i) -> ("(" <> n <> ", " <> k <> ") <- PegRt.label " <> hsString n <> " (" <> e <> ")\n          ; PegRt.touch " <> n, k)
    _ -> ("(_, " <> k <> ") <- " <> e, k)

exprCodeS :: Env -> Expr -> Gen Text
exprCodeS env = exprCodeSU env True

-- 'exprCodeU' for grammars with @%syntax@.
exprCodeSU :: Env -> Bool -> Expr -> Gen Text
exprCodeSU env used expr = case expr of
  ELit {} -> plainOf
  EClass {} -> plainOf
  EAny -> plainOf
  EPred {} -> plainOf
  ERef {} -> exprCode env expr
  EGroup alts
    | used && hasValue (units env) expr -> do
        bodies <- mapM (\is -> passThroughS env False is >>= \(stmts, v, ks) -> pure (doReturn stmts v ks)) alts
        pure ("PegRt.choice [" <> T.intercalate ", " bodies <> "]")
    | otherwise -> do
        bodies <- mapM (\is -> mapM (itemStmtS env False) is >>= \rs -> pure (doReturn (map fst rs) "()" (map snd rs))) alts
        pure ("PegRt.choice [" <> T.intercalate ", " bodies <> "]")
  EStar x -> wrap "PegRt.manyS" used x
  EPlus x -> wrap "PegRt.many1S" used x
  EOpt x -> wrap "PegRt.optionalS" used x
  EAnd x -> wrap "PegRt.plain PegPrelude.. PegRt.andP" False x
  ENot x -> wrap "PegRt.plain PegPrelude.. PegRt.notP" False x
  ECapture x -> wrap "PegRt.captureS" False x
  ELabel _ x name -> do
    e <- exprCodeSU env used x
    pure ("PegRt.labeledS " <> hsString name <> " " <> recoveryCode env True (used && hasValue (units env) x) name <> " (" <> e <> ")")
  EDiscard x -> wrap "PegRt.voidS" False x
  ETemplate {} -> error "a template call must be expanded before generating code: call Peg.Grammar.Templates.expandTemplates first"
  where
    plainOf = do
      e <- exprCode env expr
      pure ("PegRt.plain (" <> e <> ")")
    wrap f inner x = do
      e <- exprCodeSU env inner x
      pure ("(" <> f <> ") (" <> e <> ")")

-- The recovery parser for a label, if the grammar gives one (ADR 0021). A
-- label on an expression without a value discards the recovery's value.
recoveryCode :: Env -> Bool -> Bool -> Text -> Text
recoveryCode env syntaxMode valued name =
  case [unLoc r | (Located _ l, r) <- grammarRecovers (envGrammar env), l == name] of
    r : _
      | valued -> "(PegPrelude.Just " <> ruleVar r <> ")"
      | syntaxMode -> "(PegPrelude.Just (PegRt.voidS " <> ruleVar r <> "))"
      | otherwise -> "(PegPrelude.Just (PegRt.voidP " <> ruleVar r <> "))"
    [] -> "PegPrelude.Nothing"
