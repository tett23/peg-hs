{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Importing the rules of libraries (ADR 0092).
--
-- A library is a grammar file with @%library@ and without @%module@; it
-- has only comments and rules besides it. A grammar imports a library with
-- @%import lex\/Ident.hpeg@, a path relative to the directory of the
-- grammar ('Peg.Grammar.Assemble.isImportPath'). A library imports
-- nothing, so imports are one level deep.
--
-- 'resolveImports' puts the rules of the libraries into the grammar, from
-- their texts; it reads no file. "Peg.Grammar.Import.Files" reads the
-- texts from the files, and the wasm reactor takes them in its requests.
--
-- @
-- case parseGrammar src of
--   Left diags -> mapM_ (TIO.putStrLn . renderDiagnostic file []) diags
--   Right g0 -> do
--     texts <- either (const []) id \<$> readImports file g0
--     case resolveImports g0 texts >>= expandTemplates >>= check of
--       Left diags -> mapM_ (TIO.putStrLn . renderDiagnostic file (grammarImports g0)) diags
--       Right analysis -> print (analysisStart analysis)
-- @
module Peg.Grammar.Import
  ( importPaths
  , resolveImports
  , libraryErrors
  , isImportPath
  ) where

import Data.Either (partitionEithers)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust, maybeToList)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Assemble (Top (..), assemble, isImportPath)
import Peg.Grammar.Check (checkLibrary)
import Peg.Grammar.Parser (parseTops)
import Peg.Grammar.Templates (expandTemplates, templateNotes)

-- | The paths of the libraries that a grammar imports, in the order of its
-- @%import@s, at the locations of the directives. The parser has checked
-- their form ('isImportPath') and that none is imported twice.
importPaths :: Grammar -> [Located FilePath]
importPaths = grammarImports

-- | The grammar with the rules of the libraries it imports, given the text
-- of each path of 'importPaths'. The rules are those of the grammar, then
-- those of each library in the order of the @%import@s; the locations in
-- the @i@-th library have 'locFile' @i@. A rule of a library that the
-- grammar cannot reach, from its rules, from the rules its directives name
-- and from those, is left out: it is not an error and is not generated.
--
-- The errors are
--
-- * @missing %module directive@ for a library given as the grammar;
-- * at an @%import@, @cannot import lex\/Ident.hpeg: no such file@ for a
--   path without a text, and
--   @lex\/Ident.hpeg is not a library: it has no %library directive@;
-- * the errors of a library on its own ('libraryErrors'), in the library;
-- * @duplicate definition of Ident@ for a rule of the name of a rule read
--   before it, in the grammar or in an earlier library.
--
-- A library calls only its own rules, so a call of a rule of the grammar
-- or of another library is an @undefined rule@ in the library.
resolveImports :: Grammar -> [(FilePath, Text)] -> Either [Diagnostic] Grammar
resolveImports root texts
  | isJust (grammarLibrary root) = Left [Diagnostic (Loc 0 1 1) "missing %module directive"]
  | otherwise = case partitionEithers (zipWith library [1 ..] (grammarImports root)) of
      ([], libs) -> merge (grammarRules root ++ concat libs)
      (errs, _) -> Left (sortOn diagLoc (concat errs))
  where
    library i (Located l p) = case lookup p texts of
      Nothing -> Left [Diagnostic l ("cannot import " <> T.pack p <> ": no such file")]
      Just text -> case parseTops text of
        Left ds -> Left (map (inFile i) ds)
        Right tops
          | null [() | TDirective _ "library" _ _ <- tops] ->
              Left [Diagnostic l (T.pack p <> " is not a library: it has no %library directive")]
          | otherwise -> case assemble tops of
              Left ds -> Left (map (inFile i) ds)
              Right g -> case libraryErrors g of
                [] -> Right (map (relocateRule i) (grammarRules g))
                ds -> Left (map (inFile i) ds)
    merge rules = case duplicates rules of
      [] -> Right root {grammarRules = filter (kept rules) rules}
      ds -> Left ds
    kept rules =
      let reached = reachable rules (map ruleName (grammarRules root) ++ directiveRules root)
       in \r -> locFile (ruleLoc r) == 0 || S.member (ruleName r) reached

-- | The errors of a library on its own, as parsed: the errors of the
-- expansion of its templates and those of 'Peg.Grammar.Check.checkLibrary'.
libraryErrors :: Grammar -> [Diagnostic]
libraryErrors g = templateNotes g (either id checkLibrary (expandTemplates g))

-- The rules named by the directives of a grammar.
directiveRules :: Grammar -> [Text]
directiveRules g =
  map unLoc (maybeToList (grammarStart g))
    ++ map unLoc (grammarEntries g ++ grammarNoMemo g ++ grammarTokens g ++ grammarTrivia g ++ grammarInline g)
    ++ map (unLoc . snd) (grammarRecovers g)
    ++ map (unLoc . fst) (grammarExpects g)

-- The rules that names reach through the rules given.
reachable :: [Rule] -> [Text] -> S.Set Text
reachable rules = go S.empty
  where
    byName = M.fromList [(ruleName r, r) | r <- rules]
    go seen = \case
      [] -> seen
      n : ns
        | S.member n seen -> go seen ns
        | otherwise -> go (S.insert n seen) (maybe [] ruleRefs (M.lookup n byName) ++ ns)

-- The names of the rules and templates that a rule calls.
ruleRefs :: Rule -> [Text]
ruleRefs r = concatMap (concatMap (exprRefs . itemExpr) . altItems) (ruleAlts r)
  where
    exprRefs = \case
      ERef _ n _ -> [n]
      ETemplate _ n args _ -> n : concatMap exprRefs args
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

-- The definitions whose names are those of definitions before them, which
-- are in other files.
duplicates :: [Rule] -> [Diagnostic]
duplicates rules =
  [ Diagnostic (ruleLoc r) ("duplicate definition of " <> ruleName r)
  | (seen, r) <- zip (scanl (flip (S.insert . ruleName)) S.empty rules) rules
  , S.member (ruleName r) seen
  ]

-- A diagnostic in the file of the given number.
inFile :: Int -> Diagnostic -> Diagnostic
inFile i (Diagnostic l m) = Diagnostic (l {locFile = i}) m

-- A rule whose locations are in the file of the given number.
relocateRule :: Int -> Rule -> Rule
relocateRule i r =
  r
    { ruleLoc = at (ruleLoc r)
    , ruleParams = [p {paramType = located (paramType p)} | p <- ruleParams r]
    , ruleType = located (ruleType r)
    , ruleAnnotation = at <$> ruleAnnotation r
    , ruleAlts = map alt (ruleAlts r)
    }
  where
    at l = l {locFile = i}
    located (Located l x) = Located (at l) x
    alt a =
      a
        { altLoc = at (altLoc a)
        , altItems = map item (altItems a)
        , altAction = located <$> altAction a
        , altConstructor = located <$> altConstructor a
        }
    item x = x {itemLoc = at (itemLoc x), itemExpr = expr (itemExpr x)}
    expr = \case
      ERef l n args -> ERef (at l) n (map located args)
      EGroup alts -> EGroup (map (map item) alts)
      EStar x -> EStar (expr x)
      EPlus x -> EPlus (expr x)
      EOpt x -> EOpt (expr x)
      EAnd x -> EAnd (expr x)
      ENot x -> ENot (expr x)
      ECapture x -> ECapture (expr x)
      ELabel l x n -> ELabel (at l) (expr x) n
      EPred b c -> EPred b (located c)
      ETemplate l n args vs -> ETemplate (at l) n (map expr args) (map located vs)
      EDiscard x -> EDiscard (expr x)
      e -> e
