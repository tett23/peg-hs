{-# LANGUAGE LambdaCase #-}

-- Translate functions of a Haskell module of the packages into Lean, from
-- GHC's syntax tree (ADR 0097: "既存の Haskell を対象とする段階では、その関数の
-- 定義から検査可能な翻訳を作り、翻訳で扱えない構文を検出したら検証を失敗させる").
--
-- The module is read by GHC 9.10.3's own front end through the GHC API: it is
-- parsed, renamed and typechecked as the packages compile it (GHC2021 and the
-- module's LANGUAGE pragmas). The translator walks the renamed syntax tree of
-- the requested functions and of every function they reach, in the module or
-- in the other modules of the same source directories (named after their
-- module, as Peg_Grammar_reservedWords).
-- Types come from the typechecker: the type of each binder, and the type at
-- which each library function is used (which picks the instance of a class
-- method). A construct outside the subset below stops the translation with
-- its source location; nothing is skipped or approximated.
--
-- The subset (README, "GHC の構文木からの翻訳" and premise X2):
-- - Function bindings with several equations; patterns (variables,
--   wildcards, constructors in prefix, infix and record form, tuples, lists,
--   integer, character and string literals, as-patterns, bang patterns,
--   parentheses); guards (boolean guards, pattern guards, let); where
--   bindings. Equations and guards are tried in order and fall through as in
--   Haskell; falling off the end gives `hsUndefined`, the default value of
--   the type (Haskell raises an error there).
-- - Local function bindings are lifted to top-level definitions that take
--   the local variables they use as leading arguments. A local value
--   binding becomes a `let`; a recursive local value is rejected. The hint
--   `lift NAME` lifts the local values of NAME too, so that proofs can name
--   them. A local function generalised with class constraints is translated
--   once for each type that it is used at outside its recursive group.
-- - Expressions: variables, constructors, application, operators (with
--   GHC's fixities), sections, lambda, \case, case, if, multi-way if, let,
--   tuples, lists, list comprehensions, do-blocks (the bind of the block's
--   monad, by its type), record construction, update and field selection,
--   literals, type signatures, `zip [n ..] xs` (the only infinite list) and
--   `[a .. b]`.
-- - Data and newtype declarations of the module and of the modules it
--   imports from the same source directory, as Lean inductive types, when a
--   translated function's types reach them. A type that derives Eq gets
--   Lean's derived BEq; equality at any other project type is rejected.
-- - Instances of Functor, Applicative and Monad declared in the module: each
--   method is a definition; a use of the method at that type, and a do-block
--   in that monad, call the definitions (with base's default methods).
-- - Recursion: Lean must prove every recursive group terminating, possibly
--   with a termination_by/decreasing_by text from the hints file (Lean checks
--   it), or the group is in the hints file's fuel list. The hint
--   `equations NAME` makes the matches and pattern bindings of NAME keep the
--   equations of their values (`match h : x with`), for the decreasing
--   proofs; the value is the same. A function of a fuel
--   group takes a fuel argument first; a call inside the group spends one;
--   an empty fuel gives `hsUndefined`; a caller outside the group passes its
--   own fuel, and so takes one too. The fuel translation agrees with the
--   Haskell function at every large enough fuel when the Haskell evaluation
--   terminates (rule H6 of HsPrelude.lean).
-- - Library functions: the table `library` maps each (module, name, type) to
--   a function of HsPrelude.lean. That each pair computes the same value is
--   an evaluation rule (HsPrelude.lean lists them); a name outside the table
--   is rejected.
--
-- Usage: TranslateHaskell LIBDIR SRCDIRS MODULE NAMESPACE HINTS ROOT...
-- (SRCDIRS: source directories separated by colons)
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM, unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isAlphaNum, ord)
import Data.Data (Data, cast, gmapQ)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.IORef
import Data.List (intercalate, isPrefixOf, nub, sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Set as S
import GHC
import GHC.Core.DataCon (dataConName, dataConOrigArgTys)
import GHC.Core.TyCo.Rep (Type (..), scaledThing)
import GHC.Driver.Flags (Language (..))
import GHC.Unit.Module.ModSummary (msHsFilePath)
import GHC.Core.TyCon (isTupleTyCon, tyConName)
import GHC.Core.Unify (tcMatchTy)
import GHC.Core.TyCo.Subst (Subst, substTy)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.Type (expandTypeSynonyms, getTyVar_maybe, splitFunTy_maybe, splitTyConApp_maybe, tyCoVarsOfType)
import GHC.Data.Bag (bagToList)
import GHC.Data.FastString (unpackFS)
import GHC.Driver.Session (lang_set)
import GHC.Hs.Syn.Type (lhsExprType)
import GHC.Types.Basic (Boxity (..), RecFlag (..))
import GHC.Types.FieldLabel (flSelector)
import GHC.Types.Name (nameOccName, nameUnique, nameModule_maybe, isInternalName)
import GHC.Types.Name.Occurrence (occNameString)
import GHC.Types.SourceText (IntegralLit (..))
import GHC.Types.Unique (getKey)
import GHC.Types.Var (Var, isInvisibleFunArg, tyVarName, varName, varType)
import GHC.Types.Unique.Set (nonDetEltsUniqSet)
import GHC.Utils.Outputable (showPprUnsafe)
import System.Environment (getArgs)
import System.Exit (die)

-- Failure ----------------------------------------------------------------------------

-- ExceptT String IO, by hand.
newtype X a = X {runX :: IO (Either String a)}

instance Functor X where
  fmap f (X m) = X (fmap (fmap f) m)

instance Applicative X where
  pure = X . pure . Right
  X f <*> X a = X $ f >>= either (pure . Left) (\g -> fmap (fmap g) a)

instance Monad X where
  X m >>= k = X $ m >>= either (pure . Left) (runX . k)

io :: IO a -> X a
io = X . fmap Right

bad :: SrcSpan -> String -> X a
bad sp msg = X (pure (Left (showPprUnsafe sp ++ ": unsupported: " ++ msg)))

badN :: String -> X a
badN msg = X (pure (Left ("unsupported: " ++ msg)))

-- Names ------------------------------------------------------------------------------

leanReserved :: S.Set String
leanReserved =
  S.fromList
    [ "at", "fun", "end", "then", "do", "by", "have", "show", "from", "open", "in", "if", "else", "let", "match"
    , "with", "where", "deriving", "instance", "class", "structure", "def", "theorem", "namespace", "section"
    , "variable", "universe", "import", "mutual", "local", "private", "protected", "notation", "infix", "macro"
    , "syntax", "this", "Type", "Prop", "Sort", "none", "some", "id", "default", "true", "false", "not", "fst"
    , "snd", "rfl", "return", "for", "unless", "try", "catch", "finally", "break", "continue", "mut", "suffices"
    , "calc", "nomatch", "abbrev", "inductive", "axiom", "opaque", "example", "attribute", "export", "using"
    , "and", "or", "max", "min", "const", "flip", "map", "filter", "length", "take", "drop", "zip", "all", "any"
    , "fuel", "partial", "termination_by", "decreasing_by", "omit", "include", "fail", "pure", "bind"
    , "prefix", "postfix", "infixl", "infixr", "elab", "elab_rules", "macro_rules", "declare_syntax_cat"
    , "noncomputable", "unsafe", "theorem", "lemma", "opaque", "where", "extends", "renaming", "hiding"
    , "begin", "obtain", "assume", "sorry", "admit", "Sort", "Type", "deriving", "init", "next"
    ]

sanitize :: String -> String
sanitize s
  | S.member s leanReserved = s ++ "_"
  | all (\c -> isAlphaNum c || c == '_' || c == '\'') s, take 1 s /= "'" = s
  | otherwise = "«" ++ s ++ "»"

-- Type variables live apart from term variables in Haskell, not in Lean.
tyVarLean :: Name -> String
tyVarLean v = "τ" ++ filter (\c -> isAlphaNum c || c == '_') (occ v)

occ :: Name -> String
occ = occNameString . nameOccName

nkey :: Name -> Int
nkey = fromIntegral . getKey . nameUnique

modOf :: Name -> String
modOf n = maybe "" (normal . moduleNameString . moduleName) (nameModule_maybe n)
  where
    -- base 4.20 re-exports ghc-internal's modules.
    normal m
      | "GHC.Internal.Data." `isPrefixOf` m = drop 13 m
      | "GHC.Internal." `isPrefixOf` m = "GHC." ++ drop 13 m
      | otherwise = m

-- The global tables ----------------------------------------------------------------

data ConInfo = ConInfo
  { ciLean :: String -- Lean constructor, Type.Con
  , ciType :: String -- Lean type name
  , ciArity :: Int
  , ciFields :: [String] -- Haskell field names in order ([] when positional)
  , ciAlone :: Bool -- the only constructor of its type
  , ciSiblings :: [(String, Int)] -- the constructors of its type, with their arities
  }

data Def = Def
  { dName :: Name -- the Haskell binder
  , dLean :: String
  , dBind :: HsBind GhcRn
  , dCaptured :: [Name] -- local variables taken as leading arguments
  , dSpan :: SrcSpan
  , dArity :: Int -- the arguments of its equations
  , dInstance :: Bool -- a method of an instance of the module
  }

data G = G
  { gTypes :: M.Map Int Type -- binder types by name unique
  , gExprTypes :: M.Map RealSrcSpan Type -- types of expressions by span (outermost)
  , gCons :: M.Map String ConInfo -- by Haskell constructor name (module.occ)
  , gFields :: M.Map String (ConInfo, Int) -- Haskell field name -> constructor and index
  , gDefs :: M.Map Int Def -- translated functions, by name unique
  , gFuel :: M.Map Int String -- function -> fuel group id
  , gInstances :: M.Map (String, String) String -- (tycon, method) -> Lean name
  , gProject :: S.Set String -- project modules
  , gEqTypes :: S.Set String -- project types deriving Eq (module.occ)
  , gOrdTypes :: S.Set String -- project types deriving Ord (module.occ)
  , gTyCons :: IORef (M.Map String TyCon) -- project type constructors met
  , gFresh :: IORef Int
  , gLibraryUsed :: IORef (S.Set String)
  , gSubst :: Maybe Subst -- the specialisation of the definition being translated
  , gSpecial :: M.Map Int (Int, [(Type, Subst)]) -- constrained local functions: their group and copies
  , gCopy :: M.Map Int Int -- the copy of each constrained group being translated
  , gNamespace :: String
  , gHints :: M.Map String String -- Lean name without the line -> termination_by/decreasing_by
  , gEquations :: S.Set String -- definitions whose pattern bindings keep their equation
  , gEquationHere :: Bool -- the definition being translated is one of them
  , gBefore :: M.Map String String -- Lean name without the line -> lemmas before the definition
  }

qual :: Name -> String
qual n = modOf n ++ "." ++ occ n

fresh :: G -> X String
fresh g = io $ do
  n <- readIORef (gFresh g)
  writeIORef (gFresh g) (n + 1)
  pure ("ν" ++ show n)

-- Types ------------------------------------------------------------------------------

leanType :: G -> Type -> X String
leanType g ty0 = go (expandTypeSynonyms ty0)
  where
    go ty
      | (tvs@(_ : _), body) <- splitForAllTyCoVars ty = do
          b <- go body
          pure ("(" ++ concat ["{" ++ tyVarLean (tyVarName tv) ++ " : Type} → " | tv <- tvs] ++ b ++ ")")
      | Just v <- getTyVar_maybe ty = pure (tyVarLean (tyVarName v))
      | Just (af, _, a, r) <- splitFunTy_maybe ty = do
          when (isInvisibleFunArg af) (badN ("a constraint in the type " ++ showPprUnsafe ty0))
          a' <- go a
          r' <- go r
          pure ("(" ++ a' ++ " → " ++ r' ++ ")")
      | Just (tc, args) <- splitTyConApp_maybe ty = do
          as' <- mapM go args
          let n = tyConName tc
              appT f xs = if null xs then f else "(" ++ unwords (f : xs) ++ ")"
          case (modOf n, occ n, as') of
            ("GHC.Types", "Int", []) -> pure "Int"
            ("GHC.Types", "Bool", []) -> pure "Bool"
            ("GHC.Types", "Char", []) -> pure "HsChar"
            ("Data.Text.Internal", "Text", []) -> pure "String"
            ("GHC.Types", "List", [a]) -> pure (appT "List" [a])
            ("GHC.Maybe", "Maybe", [a]) -> pure (appT "Option" [a])
            ("Data.Either", "Either", [a, b]) -> pure (appT "Except" [a, b])
            ("GHC.Num.Integer", "Integer", []) -> pure "Int"
            ("GHC.Num.Natural", "Natural", []) -> pure "Nat"
            ("GHC.Unicode", "GeneralCategory", []) -> pure "HsGeneralCategory"
            (m, "Unit", []) | "GHC.Tuple" `isPrefixOf` m -> pure "Unit"
            ("Data.Map.Internal", "Map", [k, v]) -> pure (appT "HsMap" [k, v])
            ("Data.Set.Internal", "Set", [a]) -> pure (appT "HsSet" [a])
            ("Data.Graph", "SCC", [a]) -> pure (appT "HsSCC" [a])
            (_, _, xs) | isTupleTyCon tc, length xs >= 2 -> pure ("(" ++ intercalate " × " xs ++ ")")
            (m, o, xs) | S.member m (gProject g) -> do
              io (modifyIORef (gTyCons g) (M.insert (qual n) tc))
              pure (appT (gNamespace g ++ "." ++ sanitize o) xs)
            (m, o, _) -> badN ("the type " ++ m ++ "." ++ o)
      | otherwise = badN ("the type " ++ showPprUnsafe ty0)

-- Split a function type into n argument types and the result, after the
-- foralls; returns the type variables too.
splitArgs :: Int -> Type -> Maybe ([Var], [Type], Type)
splitArgs n ty0 =
  let (tvs, body) = splitForAllTyCoVars (expandTypeSynonyms ty0)
   in fmap (\(as, r) -> (tvs, as, r)) (go n body)
  where
    go 0 t = Just ([], t)
    go k t = case splitFunTy_maybe t of
      Just (af, _, a, r) | not (isInvisibleFunArg af) -> fmap (\(as, res) -> (a : as, res)) (go (k - 1) r)
      _ -> Nothing

headOf :: Type -> String
headOf ty = case splitTyConApp_maybe (expandTypeSynonyms ty) of
  Just (tc, _) -> qual (tyConName tc)
  Nothing -> case ty of
    AppTy f _ -> headOf f
    _ -> "?"

-- The head of the nth argument (from 0) of a function type, or of the
-- result after n arguments.
argHead, resHead :: Int -> Type -> String
argHead n ty = case splitArgs (n + 1) ty of
  Just (_, as, _) -> headOf (last as)
  Nothing -> "?"
resHead n ty = case splitArgs n ty of
  Just (_, _, r) -> headOf r
  Nothing -> "?"

tText, tList, tMaybe, tInt, tChar, tBool, tEither, tInteger, tNatural :: String
tEither = "Data.Either.Either"
tInteger = "GHC.Num.Integer.Integer"
tNatural = "GHC.Num.Natural.Natural"
tText = "Data.Text.Internal.Text"
tList = "GHC.Types.List"
tMaybe = "GHC.Maybe.Maybe"
tInt = "GHC.Types.Int"
tChar = "GHC.Types.Char"
tBool = "GHC.Types.Bool"

-- Whether `==` at a type is translated: builtins, Map, Set, tuples, and
-- project types deriving Eq.
eqAllowed :: G -> Type -> Bool
eqAllowed g t = case splitTyConApp_maybe (expandTypeSynonyms t) of
  Just (tc, args) ->
    let n = qual (tyConName tc)
        ok =
          n `elem` [tText, tList, tMaybe, tInt, tChar, tBool, tEither, tInteger, tNatural, "GHC.Unicode.GeneralCategory", "Data.Map.Internal.Map", "Data.Set.Internal.Set"]
            || isTupleTyCon tc
            || S.member n (gEqTypes g)
     in ok && all (eqAllowed g) args
  Nothing -> False

-- The library ------------------------------------------------------------------------

-- A library name at the type of its occurrence, as a Lean function.
library :: G -> String -> String -> Maybe Type -> Maybe String
library g m o mty = case o of
  _ | not known -> Nothing
  "map" | base -> Just "List.map"
  "filter" | base -> Just "List.filter"
  "++" | base -> Just "HsList.append"
  "zip" | base -> Just "List.zip"
  "take" | base, a0 == tInt -> Just "HsList.take"
  "drop" | base, a0 == tInt -> Just "HsList.drop"
  "fst" | base -> Just "Prod.fst"
  "snd" | base -> Just "Prod.snd"
  "uncurry" | base -> Just "HsBase.uncurry"
  "const" | base -> Just "HsBase.const"
  "flip" | base -> Just "HsBase.flip"
  "id" | base -> Just "HsBase.id"
  "." | base -> Just "HsBase.comp"
  "$" | base -> Just "HsBase.apply"
  "not" | base -> Just "HsBase.not"
  "&&" | base -> Just "HsBase.and"
  "||" | base -> Just "HsBase.or"
  "otherwise" | base -> Just "true"
  "maybe" | base -> Just "HsBase.maybe"
  "catMaybes" | base -> Just "HsList.catMaybes"
  "seq" | base -> Just "HsBase.seq"
  "concat" | base, a0 == tList -> Just "HsList.concat"
  "concatMap" | base, a1 == tList -> Just "HsList.concatMap"
  "and" | base, a0 == tList -> Just "HsList.and"
  "any" | base, a1 == tList -> Just "HsList.any"
  "all" | base, a1 == tList -> Just "HsList.all"
  "elem" | base, a1 == tList, eqArg 0 -> Just "HsList.elem"
  "notElem" | base, a1 == tList, eqArg 0 -> Just "HsList.notElem"
  "null" | base, a0 == tList -> Just "HsList.null"
  "length" | base, a0 == tList -> Just "HsList.length"
  "foldr" | base, a2 == tList -> Just "HsList.foldr"
  "sortOn" | base, ordArg -> Just "HsList.sortOn"
  -- Rule H11: a key of a project type that derives Ord.
  "sortOn" | base, derivedOrdArg -> Just "HsList.sortOnOrd"
  "fromEnum" | base, a0 == tChar -> Just "HsChar.fromEnum"
  "max" | base, a0 == tInt -> Just "HsInt.max"
  "min" | base, a0 == tInt -> Just "HsInt.min"
  "show" | base, a0 == tInt -> Just "HsInt.«show»"
  -- Rule H7: show at another type is only compared for equality (the key of
  -- a set); it becomes Lean's Repr, and both are injective.
  "show" | base, eqArg 0 -> Just "HsShow.viaRepr"
  "==" | base, eqArg 0 -> Just "HsBase.eq"
  "/=" | base, eqArg 0 -> Just "HsBase.ne"
  "<" | base, integral a0 -> Just "HsInt.lt"
  "<=" | base, integral a0 -> Just "HsInt.le"
  ">" | base, integral a0 -> Just "HsInt.gt"
  ">=" | base, integral a0 -> Just "HsInt.ge"
  "<=" | base, a0 == tChar -> Just "HsChar.le"
  "<" | base, a0 == tChar -> Just "HsChar.lt"
  "*" | base, integral a0 -> Just "HsInt.mul"
  "div" | base, integral a0 -> Just "HsInt.div"
  "toInteger" | base, a0 == tInt -> Just "HsInt.toInteger"
  "fromInteger" | base, a0 == tInteger, r0' == tInt -> Just "HsInt.fromInteger"
  "maxBound" | base, maybe "?" headOf mty == tInt -> Just "HsInt.maxBound"
  "reverse" | base, a0 == tList -> Just "HsList.reverse"
  "lookup" | base, a1 == tList, eqArg 0 -> Just "HsList.lookup"
  "span" | base, a1 == tList -> Just "HsList.span"
  "break" | base, a1 == tList -> Just "HsList.break"
  "foldl" | base, a2 == tList -> Just "HsList.foldl"
  "foldM" | base, a2 == tList, r3 == tMaybe -> Just "HsMaybe.foldM"
  "isJust" | base -> Just "HsMaybe.isJust"
  "pure" | base, r0' == tList -> Just "HsList.pure"
  "pure" | base, r0' == tEither -> Just "HsEither.pure"
  ">>=" | base, a0 == tEither -> Just "HsEither.bind"
  "<$>" | base, a1 == tEither -> Just "HsEither.fmap"
  "fmap" | base, a1 == tEither -> Just "HsEither.fmap"
  "chr" | base -> Just "HsChar.chr"
  "digitToInt" | base -> Just "HsChar.digitToInt"
  f | m == "GHC.Unicode", f `elem` ["isSpace", "isUpper", "isDigit", "isHexDigit", "isAscii", "isAsciiUpper", "generalCategory"] -> Just ("HsChar." ++ f)
  "+" | base, integral a0 -> Just "HsInt.add"
  "-" | base, integral a0 -> Just "HsInt.sub"
  "negate" | base, integral a0 -> Just "HsInt.neg"
  "<>" | base, a0 == tText -> Just "HsText.append"
  "<$>" | base, a1 == tMaybe -> Just "HsMaybe.fmap"
  "fmap" | base, a1 == tMaybe -> Just "HsMaybe.fmap"
  "<*>" | base, a0 == tMaybe -> Just "HsMaybe.ap"
  ">>=" | base, a0 == tMaybe -> Just "HsMaybe.bind"
  "pure" | base, r0' == tMaybe -> Just "HsMaybe.pure"
  "mapM" | base, a1 == tList, r2 == tMaybe -> Just "HsMaybe.mapM"
  "sequence" | base, a0 == tList, r0' == tList -> Just "HsList.sequence"
  "uncons" | text -> Just "HsText.uncons"
  "null" | text -> Just "HsText.null"
  "strip" | text -> Just "HsText.strip"
  "split" | text -> Just "HsText.split"
  "pack" | text -> Just "HsText.pack"
  "length" | text -> Just "HsText.length"
  "take" | text -> Just "HsText.take"
  "drop" | text -> Just "HsText.drop"
  "span" | text -> Just "HsText.span"
  "break" | text -> Just "HsText.«break»"
  "all" | text -> Just "HsText.all"
  "isInfixOf" | text -> Just "HsText.isInfixOf"
  "concat" | text -> Just "HsText.concat"
  f | text, f `elem` textFunctions -> Just ("HsText." ++ sanitize f)
  f | m `elem` ["Data.Map.Internal", "Data.Map.Strict.Internal"], f `elem` ["fromList", "lookup", "member", "findWithDefault", "keysSet", "fromListWith", "toList", "elems"] -> Just ("HsMap." ++ f)
  f | m == "Data.Set.Internal", f `elem` ["fromList", "member", "insert", "union", "difference", "singleton", "empty", "toList"] -> Just ("HsSet." ++ f)
  "stronglyConnComp" | m == "Data.Graph" -> Just "HsGraph.stronglyConnComp"
  "isAlpha" | m == "GHC.Unicode" -> Just "HsChar.isAlpha"
  "isAlphaNum" | m == "GHC.Unicode" -> Just "HsChar.isAlphaNum"
  _ -> Nothing
  where
    base = any (`isPrefixOf` m) ["GHC.Prim", "GHC.Base", "GHC.List", "GHC.Classes", "GHC.Num", "GHC.Show", "GHC.Enum", "Data.Foldable", "Data.Maybe", "Data.OldList", "Data.Tuple", "Data.Function", "Data.Traversable", "Data.Functor", "GHC.Maybe", "GHC.Types", "GHC.Real", "GHC.Char", "Data.Char", "Data.Either", "GHC.Control.Monad", "Control.Monad"]
    text = m `elem` ["Data.Text", "Data.Text.Show", "Data.Text.Internal"]
    known = base || text || m `elem` ["Data.Map.Internal", "Data.Map.Strict.Internal", "Data.Set.Internal", "Data.Graph", "GHC.Unicode"]
    integral a = a `elem` [tInt, tInteger]
    r3 = maybe "?" (resHead 3) mty
    -- sortOn's key of a project type that derives Ord.
    derivedOrdArg = case mty >>= splitArgs 1 of
      Just (_, [k], _) -> case splitArgs 1 k of
        Just (_, _, r) -> S.member (headOf r) (gOrdTypes g)
        Nothing -> False
      _ -> False
    a0 = maybe "?" (argHead 0) mty
    a1 = maybe "?" (argHead 1) mty
    a2 = maybe "?" (argHead 2) mty
    r2 = maybe "?" (resHead 2) mty
    r0' = maybe "?" (resHead 1) mty
    eqArg n = case mty >>= splitArgs (n + 1) of
      Just (_, as, _) -> eqAllowed g (last as)
      Nothing -> False
    -- sortOn's key must be Int (the only order translated).
    ordArg = case mty >>= splitArgs 1 of
      Just (_, [k], _) -> case splitArgs 1 k of
        Just (_, _, r) -> headOf r == tInt
        Nothing -> False
      _ -> False

-- The functions of Data.Text translated as HsText.NAME (rule H3, H12).
textFunctions :: [String]
textFunctions =
  [ "foldl'", "breakOn", "takeWhile", "stripStart", "stripEnd", "splitAt", "unpack", "singleton", "any", "words"
  , "splitOn", "isSuffixOf", "takeWhileEnd", "breakOnEnd", "dropEnd"
  ]

-- Literals ---------------------------------------------------------------------------

intLit :: Integer -> String
intLit n = "(" ++ show n ++ " : Int)"

charLit :: Char -> String
charLit ch = "(HsChar.ofNat " ++ show (ord ch) ++ ")"

stringLit :: String -> String
stringLit s = "\"" ++ concatMap esc s ++ "\""
  where
    esc ch
      | ch == '"' = "\\\""
      | ch == '\\' = "\\\\"
      | ord ch >= 0x20 && ord ch < 0x7f = [ch]
      | otherwise = "\\u{" ++ hex (ord ch) ++ "}"
    hex n = if n < 16 then [digit n] else hex (n `div` 16) ++ [digit (n `mod` 16)]
    digit k = "0123456789abcdef" !! k

-- The type at an expression's span, when the typechecker recorded one.
typeAt :: G -> SrcSpan -> Maybe Type
typeAt g sp = case sp of
  RealSrcSpan r _ -> fmap (specialise g) (M.lookup r (gExprTypes g))
  _ -> Nothing

specialise :: G -> Type -> Type
specialise g t = maybe t (\su -> substTy su t) (gSubst g)

-- The type of a binder, specialised.
binderType :: G -> Name -> Maybe Type
binderType g n = case M.lookup (nkey n) (gSpecial g) of
  Just (grp, copies) -> fmap fst (lookup (M.findWithDefault 0 grp (gCopy g)) (zip [0 ..] copies))
  Nothing -> fmap (specialise g) (M.lookup (nkey n) (gTypes g))

-- Scopes ----------------------------------------------------------------------------

data Scope = Scope
  { sFuel :: Maybe String -- the fuel variable
  , sGroup :: Maybe String -- the fuel group of the definition
  , sExtra :: [String] -- arguments that the right-hand sides are applied to
  }

-- Expressions --------------------------------------------------------------------

app :: String -> [String] -> String
app f [] = f
app f as = "(" ++ unwords (f : as) ++ ")"

expr :: G -> Scope -> LHsExpr GhcRn -> X String
expr g sc (L l e) = case e of
  HsVar _ (L nl n) -> saturate g sc (locA nl) n []
  HsRecSel _ fo -> field g (locA l) (occ (foExt fo))
  HsApp {} -> do
    let (f, as) = spine (L l e)
    case (f, as) of
      (L _ (HsVar _ (L _ z)), [L _ (ArithSeq _ Nothing (From n)), xs])
        | occ z == "zip" && "GHC." `isPrefixOf` modOf z -> do
            n' <- expr g sc n
            xs' <- expr g sc xs
            io (modifyIORef (gLibraryUsed g) (S.insert "HsList.zipFrom"))
            pure (app "HsList.zipFrom" [n', xs'])
      (L _ (HsVar _ (L nl n)), _) -> do
        as' <- mapM (expr g sc) as
        saturate g sc (locA nl) n as'
      _ -> do
        f' <- expr g sc f
        as' <- mapM (expr g sc) as
        pure (app f' as')
  OpApp _ a (L _ (HsVar _ (L _ n))) b
    | occ n == "." && isBase n -> do
        v <- fresh g
        inner <- exprApplied g sc b [v]
        outer <- exprApplied g sc a [inner]
        pure ("(fun " ++ v ++ " => " ++ outer ++ ")")
    | occ n == "$" && isBase n -> do
        b' <- expr g sc b
        exprApplied g sc a [b']
  OpApp _ a op b -> do
    a' <- expr g sc a
    b' <- expr g sc b
    case op of
      L _ (HsVar _ (L nl n)) -> saturate g sc (locA nl) n [a', b']
      _ -> do
        op' <- expr g sc op
        pure (app op' [a', b'])
  NegApp _ a _ -> do
    a' <- expr g sc a
    pure (app "HsInt.neg" [a'])
  HsPar _ a -> expr g sc a
  SectionL _ a op -> do
    a' <- expr g sc a
    case op of
      L _ (HsVar _ (L nl n)) -> saturate g sc (locA nl) n [a']
      _ -> do
        op' <- expr g sc op
        pure (app op' [a'])
  SectionR _ op b -> do
    v <- fresh g
    op' <- expr g sc op
    b' <- expr g sc b
    pure ("(fun " ++ v ++ " => " ++ app op' [v, b'] ++ ")")
  ExplicitTuple _ args Boxed -> do
    xs <- forM args $ \case
      Present _ a -> expr g sc a
      _ -> bad (locA l) "a tuple section"
    pure ("(" ++ intercalate ", " xs ++ ")")
  ExplicitList _ xs -> do
    xs' <- mapM (expr g sc) xs
    pure ("[" ++ intercalate ", " xs' ++ "]")
  HsOverLit _ ol -> overLit g (locA l) ol
  HsLit _ lit -> litE (locA l) lit
  HsLam _ LamSingle mg -> lambda g sc (locA l) mg
  HsLam _ LamCase mg -> do
    v <- fresh g
    body <- matchGroup g sc [v] mg "hsUndefined"
    tyAnn <- lamArgs g (locA l) 1
    pure ("(fun " ++ binder v (head' tyAnn) ++ " => " ++ body ++ ")")
  HsCase _ scrut mg -> do
    s <- expr g sc scrut
    v <- fresh g
    body <- matchGroup g sc [v] mg "hsUndefined"
    pure ("(let " ++ v ++ " := " ++ s ++ "; " ++ body ++ ")")
  HsIf _ c t f -> do
    c' <- expr g sc c
    t' <- expr g sc t
    f' <- expr g sc f
    pure ("(if " ++ c' ++ " then " ++ t' ++ " else " ++ f' ++ ")")
  HsMultiIf _ alts -> guardsChain g sc alts "hsUndefined"
  HsLet _ binds body -> localBinds g sc binds (expr g sc body)
  HsDo _ ListComp (L _ stmts) -> listComp g sc stmts
  HsDo _ (DoExpr Nothing) (L _ stmts) -> case typeAt g (locA l) of
    Just ty -> doBlock g sc (locA l) (headOf ty) stmts
    Nothing -> bad (locA l) "a do-block whose type is unknown"
  RecordCon _ (L _ con) (HsRecFields fs Nothing) -> do
    ci <- conInfo g (locA l) con
    given <- forM fs $ \(L _ (HsFieldBind _ (L _ fo) v _)) -> do
      v' <- expr g sc v
      pure (occ (foExt fo), v')
    when (null (ciFields ci)) (bad (locA l) "a record construction of a positional constructor")
    args <- forM (ciFields ci) $ \f -> maybe (bad (locA l) ("the field " ++ f ++ " is not given")) pure (lookup f given)
    pure (app (ciLean ci) args)
  RecordUpd _ r (RegularRecUpdFields _ fs) -> do
    r' <- expr g sc r
    upd <- forM fs $ \(L _ (HsFieldBind _ (L _ afo) v _)) -> do
      v' <- expr g sc v
      let fname = case afo of
            Unambiguous n _ -> occ n
            Ambiguous _ (L _ rn) -> showPprUnsafe rn
      pure (fname, v')
    cis <- forM upd $ \(f, _) -> maybe (bad (locA l) ("the field " ++ f)) (pure . fst) (M.lookup f (gFields g))
    case (cis, nub (map ciLean cis)) of
      (ci : _, [_]) -> do
        -- The record has one constructor: the other fields are selected.
        let new = [fromMaybe (app (ciType ci ++ "." ++ sanitize f) [r']) (lookup f upd) | f <- ciFields ci]
        pure (app (ciLean ci) new)
      _ -> bad (locA l) "a record update of fields of several constructors"
  ExprWithTySig _ a _ -> expr g sc a
  -- The renamer expands some expressions (sections among them) and keeps
  -- the original, which is translated.
  XExpr (ExpandedThingRn (OrigExpr orig) _) -> expr g sc (L l orig)
  ArithSeq _ Nothing (FromTo a b) -> do
    a' <- expr g sc a
    b' <- expr g sc b
    pure (app "HsList.enumFromTo" [a', b'])
  _ -> bad (locA l) ("the expression " ++ showPprUnsafe e)
  where
    head' = \case
      x : _ -> x
      [] -> Nothing

isBase :: Name -> Bool
isBase n = modOf n `elem` ["GHC.Base"]

-- An expression applied to translated arguments: the arguments join the
-- spine, so that a translated function is not eta-expanded first.
exprApplied :: G -> Scope -> LHsExpr GhcRn -> [String] -> X String
exprApplied g sc e extra = case spine e of
  (L _ (HsVar _ (L nl n)), as) | not (occ n `elem` [".", "$"] && isBase n) -> do
    as' <- mapM (expr g sc) as
    saturate g sc (locA nl) n (as' ++ extra)
  (L _ (HsPar _ inner), []) -> exprApplied g sc inner extra
  (L _ (OpApp _ a (L _ (HsVar _ (L _ n))) b), [])
    | occ n == "." && isBase n -> do
        inner <- exprApplied g sc b extra
        exprApplied g sc a [inner]
  _ -> do
    e' <- expr g sc e
    pure (app e' extra)

spine :: LHsExpr GhcRn -> (LHsExpr GhcRn, [LHsExpr GhcRn])
spine = go []
  where
    go acc (L _ (HsApp _ f a)) = go (a : acc) f
    go acc (L _ (HsPar _ f@(L _ HsApp {}))) = go acc f
    go acc f = (f, acc)

binder :: String -> Maybe String -> String
binder v = maybe v (\t -> "(" ++ v ++ " : " ++ t ++ ")")

-- The argument types of a lambda at a span, when known.
lamArgs :: G -> SrcSpan -> Int -> X [Maybe String]
lamArgs g sp n = case typeAt g sp >>= splitArgs n of
  Just ([], as, _) -> forM as $ \a -> X (fmap (either (const (Right Nothing)) (Right . Just)) (runX (leanType g a)))
  _ -> pure (replicate n Nothing)

lambda :: G -> Scope -> SrcSpan -> MatchGroup GhcRn (LHsExpr GhcRn) -> X String
lambda g sc sp mg = case unLoc (mg_alts mg) of
  [L _ m] -> do
    let n = length (m_pats m)
    vs <- paramNames g mg n
    tys <- lamArgs g sp n
    body <- matchGroup g sc vs mg "hsUndefined"
    pure ("(fun " ++ unwords (zipWith binder vs tys) ++ " => " ++ body ++ ")")
  _ -> bad sp "a lambda with several equations"

overLit :: G -> SrcSpan -> HsOverLit GhcRn -> X String
overLit g sp ol = case ol_val ol of
  HsIntegral il
    | maybe True ((`elem` [tInt, tInteger]) . headOf) (typeAt g sp) -> pure (intLit (il_value il))
    | maybe False ((== tNatural) . headOf) (typeAt g sp), il_value il >= 0 -> pure ("(" ++ show (il_value il) ++ " : Nat)")
  HsIsString _ s
    | maybe False ((== tText) . headOf) (typeAt g sp) -> pure (stringLit (unpackFS s))
    -- A String: the list of its characters.
    | maybe False ((== tList) . headOf) (typeAt g sp) -> pure ("[" ++ intercalate ", " (map charLit (unpackFS s)) ++ "]")
  _ -> bad sp ("the literal " ++ showPprUnsafe ol ++ " at " ++ maybe "?" showPprUnsafe (typeAt g sp))

litE :: SrcSpan -> HsLit GhcRn -> X String
litE sp = \case
  HsChar _ ch -> pure (charLit ch)
  l -> bad sp ("the literal " ++ showPprUnsafe l)

field :: G -> SrcSpan -> String -> X String
field g sp f = case M.lookup f (gFields g) of
  Just (ci, i) -> pure (ciType ci ++ "." ++ sanitize f) <* pure i
  Nothing -> bad sp ("the field " ++ f)

conInfo :: G -> SrcSpan -> Name -> X ConInfo
conInfo g sp n = maybe (bad sp ("the constructor " ++ qual n)) pure (M.lookup (qual n) (gCons g))

-- A translated function applied to fewer arguments than its equations take
-- is eta-expanded, so that Lean's termination checker sees each call.
saturate :: G -> Scope -> SrcSpan -> Name -> [String] -> X String
saturate g sc sp n as = do
  f <- var g sc sp n
  case (f, as) of
    -- Composition and application are applied in place, so that the
    -- functions they take stay visible to Lean's termination checker.
    ("HsBase.comp", f1 : g1 : x : rest) -> pure (app f1 [app g1 [x]] `app'` rest)
    ("HsBase.comp", [f1, g1]) -> do
      v <- fresh g
      pure ("(fun " ++ v ++ " => " ++ app f1 [app g1 [v]] ++ ")")
    ("HsBase.apply", f1 : x : rest) -> pure (app f1 [x] `app'` rest)
    _ -> saturate' g f n as

app' :: String -> [String] -> String
app' f [] = f
app' f as = app f as

saturate' :: G -> String -> Name -> [String] -> X String
saturate' g f n as = do
  let arity = case M.lookup (nkey n) (gDefs g) of
        Just d | not (dInstance d) -> dArity d
        _ -> fromMaybe 0 (lookup f higherOrder)
  if arity > length as
    then do
      extra <- mapM (const (fresh g)) [1 .. arity - length as]
      pure ("(fun " ++ unwords extra ++ " => " ++ app f (as ++ extra) ++ ")")
    else pure (app f as)

-- Library functions that take functions, with their arities: a partial
-- application is eta-expanded too, so that the function argument is a
-- lambda that Lean's termination checker can attach membership to.
higherOrder :: [(String, Int)]
higherOrder =
  [ ("List.map", 2), ("List.filter", 2), ("HsList.concatMap", 2), ("HsList.any", 2), ("HsList.all", 2)
  , ("HsList.foldr", 3), ("HsMaybe.mapM", 2), ("HsBase.comp", 3), ("HsBase.maybe", 3)
  ]

-- A variable, constructor, field or library function.
var :: G -> Scope -> SrcSpan -> Name -> X String
var g sc sp n
  | Just d <- M.lookup (nkey n) (gDefs g), not (dInstance d) = do
      let callee = M.lookup (nkey n) (gFuel g)
      fuelArg <- case callee of
        Nothing -> pure []
        Just grp
          | sGroup sc == Just grp -> pure ["fuel"]
          | otherwise -> maybe (bad sp ("a call of " ++ occ n ++ " from a function without fuel")) (pure . pure) (sFuel sc)
      name <- case M.lookup (nkey n) (gSpecial g) of
        Nothing -> pure (dLean d)
        Just (grp, copies) -> case M.lookup grp (gCopy g) of
          Just i -> pure (copyName (dLean d) i (length copies))
          Nothing -> case [i | Just u <- [typeAt g sp], (i, (t, _)) <- zip [0 ..] copies, eqType t u] of
            i : _ -> pure (copyName (dLean d) i (length copies))
            [] -> bad sp ("a use of " ++ occ n ++ " at a type without a copy")
      -- A lifted function by its full name: inside its outer function, the
      -- outer name is the function being defined.
      let full = if '.' `elem` name then gNamespace g ++ "." ++ name else name
      pure (app full (fuelArg ++ map (sanitize . occ) (dCaptured d)))
  | isInternalName n = pure (sanitize (occ n))
  | otherwise = case (modOf n, occ n) of
      (_, "True") -> pure "true"
      (_, "False") -> pure "false"
      ("GHC.Maybe", "Just") -> pure "Option.some"
      ("GHC.Maybe", "Nothing") -> pure "Option.none"
      ("Data.Either", "Left") -> pure "Except.error"
      ("Data.Either", "Right") -> pure "Except.ok"
      ("GHC.Unicode", c) | c `elem` generalCategories -> pure ("HsGeneralCategory." ++ c)
      ("GHC.Types", ":") -> pure "List.cons"
      ("GHC.Types", "[]") -> pure "List.nil"
      (m, "(,)") | "GHC.Tuple" `isPrefixOf` m -> pure "Prod.mk"
      (m, "()") | "GHC.Tuple" `isPrefixOf` m -> pure "Unit.unit"
      ("Data.Graph", "AcyclicSCC") -> pure "HsSCC.AcyclicSCC"
      ("Data.Graph", "CyclicSCC") -> pure "HsSCC.CyclicSCC"
      (m, o)
        | Just ci <- M.lookup (qual n) (gCons g) -> pure (ciLean ci)
        | M.member o (gFields g), S.member m (gProject g) -> field g sp o
        | Just f <- instanceMethod g o (typeAt g sp) -> pure f
        | Just f <- library g m o (typeAt g sp) -> do
            io (modifyIORef (gLibraryUsed g) (S.insert f))
            pure f
        | otherwise -> bad sp ("the name " ++ m ++ "." ++ o ++ maybe "" ((" at " ++) . showPprUnsafe) (typeAt g sp))

-- A method of Functor, Applicative or Monad at a type whose instance the
-- module declares; (>>) is base's default, (*>), whose default is
-- (id <$ a) <*> b, and (<$) is fmap . const.
instanceMethod :: G -> String -> Maybe Type -> Maybe String
instanceMethod g o mty = do
  ty <- mty
  let at h meth = M.lookup (h, meth) (gInstances g)
  case o of
    ">>=" -> at (argHead 0 ty) ">>="
    "pure" -> at (resHead 1 ty) "pure"
    "fmap" -> at (argHead 1 ty) "fmap"
    "<$>" -> at (argHead 1 ty) "fmap"
    "<*>" -> at (argHead 0 ty) "<*>"
    ">>" -> do
      f <- at (argHead 0 ty) "fmap"
      a <- at (argHead 0 ty) "<*>"
      pure ("(fun a b => " ++ a ++ " (" ++ f ++ " (HsBase.const HsBase.id) a) b)")
    _ -> Nothing

-- Patterns ---------------------------------------------------------------------------

-- A pattern: its Lean text, the guards its literals need, and its shape for
-- the check of usefulness and exhaustiveness.
data P = P {pText :: String, pGuards :: [String], pTree :: PT}

-- The shape of a pattern: a wildcard, a constructor among its siblings (each
-- with its arity), or a literal (of an infinite type).
data PT = PAny | PCon String [(String, Int)] [PT] | PLitT

pRefutable :: P -> Bool
pRefutable p = not (null (pGuards p)) || not (exhaustive [[pTree p]] 1)

-- The constructors of Data.Char.GeneralCategory, in order.
generalCategories :: [String]
generalCategories =
  [ "UppercaseLetter", "LowercaseLetter", "TitlecaseLetter", "ModifierLetter", "OtherLetter", "NonSpacingMark"
  , "SpacingCombiningMark", "EnclosingMark", "DecimalNumber", "LetterNumber", "OtherNumber", "ConnectorPunctuation"
  , "DashPunctuation", "OpenPunctuation", "ClosePunctuation", "InitialQuote", "FinalQuote", "OtherPunctuation"
  , "MathSymbol", "CurrencySymbol", "ModifierSymbol", "OtherSymbol", "Space", "LineSeparator", "ParagraphSeparator"
  , "Control", "Format", "Surrogate", "PrivateUse", "NotAssigned"
  ]

boolSig, maybeSig, listSig, sccSig, eitherSig, categorySig :: [(String, Int)]
eitherSig = [("Except.error", 1), ("Except.ok", 1)]
categorySig = [("HsGeneralCategory." ++ c, 0) | c <- generalCategories]
boolSig = [("true", 0), ("false", 0)]
maybeSig = [("Option.none", 0), ("Option.some", 1)]
listSig = [("List.nil", 0), ("List.cons", 2)]
sccSig = [("HsSCC.AcyclicSCC", 1), ("HsSCC.CyclicSCC", 1)]

tupleCon :: Int -> String
tupleCon n = "(," ++ show n ++ ")"

pat :: G -> LPat GhcRn -> X P
pat g (L l p) = case p of
  WildPat _ -> pure (P "_" [] PAny)
  VarPat _ (L _ n) -> pure (P (sanitize (occ n)) [] PAny)
  ParPat _ q -> pat g q
  BangPat _ q -> pat g q
  AsPat _ (L _ n) q -> do
    r <- pat g q
    pure r {pText = sanitize (occ n) ++ "@" ++ pText r}
  TuplePat _ ps Boxed -> do
    rs <- mapM (pat g) ps
    let k = length rs
    pure (P ("(" ++ intercalate ", " (map pText rs) ++ ")") (concatMap pGuards rs) (PCon (tupleCon k) [(tupleCon k, k)] (map pTree rs)))
  ListPat _ ps -> do
    rs <- mapM (pat g) ps
    let tree = foldr (\r acc -> PCon "List.cons" listSig [pTree r, acc]) (PCon "List.nil" listSig []) rs
    pure (P ("[" ++ intercalate ", " (map pText rs) ++ "]") (concatMap pGuards rs) tree)
  ConPat _ (L _ n) details -> do
    (con, sig, fields) <- case (modOf n, occ n) of
      (_, "True") -> pure ("true", boolSig, [])
      (_, "False") -> pure ("false", boolSig, [])
      ("GHC.Maybe", "Just") -> pure ("Option.some", maybeSig, [])
      ("GHC.Maybe", "Nothing") -> pure ("Option.none", maybeSig, [])
      ("Data.Either", "Left") -> pure ("Except.error", eitherSig, [])
      ("Data.Either", "Right") -> pure ("Except.ok", eitherSig, [])
      ("GHC.Unicode", c) | c `elem` generalCategories -> pure ("HsGeneralCategory." ++ c, categorySig, [])
      ("GHC.Types", ":") -> pure ("List.cons", listSig, [])
      ("GHC.Types", "[]") -> pure ("List.nil", listSig, [])
      ("Data.Graph", "AcyclicSCC") -> pure ("HsSCC.AcyclicSCC", sccSig, [])
      ("Data.Graph", "CyclicSCC") -> pure ("HsSCC.CyclicSCC", sccSig, [])
      _ -> do
        ci <- conInfo g (locA l) n
        pure (ciLean ci, ciSiblings ci, ciFields ci)
    args <- case details of
      PrefixCon [] as -> mapM (pat g) as
      InfixCon a b -> mapM (pat g) [a, b]
      RecCon (HsRecFields [] Nothing) -> pure (replicate (fromMaybe 0 (lookup con sig)) (P "_" [] PAny))
      RecCon (HsRecFields fs Nothing) -> do
        given <- forM fs $ \(L _ (HsFieldBind _ (L _ fo) v _)) -> pure (occ (foExt fo), v)
        forM fields $ \f -> maybe (pure (P "_" [] PAny)) (pat g) (lookup f given)
      _ -> bad (locA l) "this constructor pattern"
    pure (P (app con (map pText args)) (concatMap pGuards args) (PCon con sig (map pTree args)))
  LitPat _ lit -> do
    v <- fresh g
    e <- litE (locA l) lit
    pure (P v [app "HsBase.eq" [v, e]] PLitT)
  NPat _ (L _ ol) Nothing _ -> do
    v <- fresh g
    e <- overLit g (locA l) ol
    pure (P v [app "HsBase.eq" [v, e]] PLitT)
  _ -> bad (locA l) ("the pattern " ++ showPprUnsafe p)

-- Usefulness of a row of patterns after the rows of a matrix (Maranget's
-- algorithm), which decides the arms of a Lean match: Lean rejects an arm
-- that no value reaches, and a match that misses a value.
useful :: [[PT]] -> [PT] -> Bool
useful rows [] = null rows
useful rows (q : qs) = case q of
  PCon c _ args -> useful (specialise' c (length args) rows) (args ++ qs)
  PLitT -> useful rows (PAny : qs)
  PAny ->
    let heads = [(c, sig) | PCon c sig _ : _ <- rows]
     in case heads of
          (_, sig) : _
            | all (\(c, _) -> c `elem` map fst heads) sig ->
                or [useful (specialise' c k rows) (replicate k PAny ++ qs) | (c, k) <- sig]
          _ -> useful (defaultRows rows) qs
  where
    specialise' c k = concatMap $ \case
      PCon c' _ args : rest | c' == c -> [args ++ rest]
      PCon {} : _ -> []
      PLitT : rest -> [replicate k PAny ++ rest]
      PAny : rest -> [replicate k PAny ++ rest]
      [] -> []
    defaultRows = concatMap $ \case
      PAny : rest -> [rest]
      PLitT : rest -> [rest]
      _ -> []

splitArm :: String -> [String]
splitArm a = words (map (\c -> if c == ',' then ' ' else c) a)

-- The names of the arguments of a match group: the variable that every
-- equation binds at a position, or a fresh name.
paramNames :: G -> MatchGroup GhcRn (LHsExpr GhcRn) -> Int -> X [String]
paramNames g mg n = forM [0 .. n - 1] $ \k -> do
  let at (L _ m) = case drop k (m_pats m) of
        L _ (VarPat _ (L _ v)) : _ -> Just (sanitize (occ v))
        _ -> Nothing
  case map at (unLoc (mg_alts mg)) of
    names@(Just v : _) | all (== Just v) names -> pure v
    _ -> fresh g

exhaustive :: [[PT]] -> Int -> Bool
exhaustive rows n = not (useful rows (replicate n PAny))

-- Whether the right-hand sides of an equation can fall through to the next
-- equation: unless its last guard is empty or `otherwise`.
canFall :: GRHSs GhcRn (LHsExpr GhcRn) -> Bool
canFall (GRHSs _ gs _) = case reverse gs of
  L _ (GRHS _ stmts _) : _ -> not (all trivially stmts)
  [] -> True
  where
    trivially (L _ (BodyStmt _ (L _ (HsVar _ (L _ n))) _ _)) = occ n `elem` ["otherwise", "True"]
    trivially (L _ (LetStmt {})) = True
    trivially _ = False

-- Matching ---------------------------------------------------------------------------

-- The equations of a match group, on the discriminant variables vs, falling
-- through to `fallback`. The equations become the arms of one Lean match, in
-- order; an equation that no value reaches first is left out of the arms
-- (it is reached only by falling through); an equation that can fall
-- through continues with the equations after it.
matchGroup :: G -> Scope -> [String] -> MatchGroup GhcRn (LHsExpr GhcRn) -> String -> X String
matchGroup g sc vs mg fallback = go (unLoc (mg_alts mg))
  where
    go eqs = do
      arms <- armsOf [] eqs
      let rows = [r | (r, _, _) <- arms]
          wildcard = [intercalate ", " (map (const "_") vs) ++ " => " ++ fallback | not (exhaustive rows (length vs))]
      case (vs, arms) of
        ([], (_, _, body) : _) -> pure body
        ([], []) -> pure fallback
        -- One arm that binds nothing new: no match.
        (_, [(_, a, body)]) | null wildcard, all (== "_") (splitArm a) -> pure body
        _ -> do
          -- The hints may ask for the equations of the discriminants, for
          -- Lean's termination checker; the discriminants then stay as they
          -- are in the arms.
          discs <-
            if gEquationHere g
              then forM vs (\v -> fmap (\h -> "h" ++ h ++ " : " ++ v) (fresh g))
              else pure vs
          pure ("(match " ++ intercalate ", " discs ++ " with" ++ concatMap ("\n  | " ++) ([a ++ " => " ++ b | (_, a, b) <- arms] ++ wildcard) ++ ")")
    armsOf _ [] = pure []
    armsOf rows (L ml m : ms) = do
      when (length (m_pats m) /= length vs) (bad (locA ml) "equations with different numbers of arguments")
      ps <- mapM (pat g) (m_pats m)
      let row = map pTree ps
          guards = concatMap pGuards ps
      if not (useful rows row)
        then armsOf rows ms
        else do
          rest <- if canFall (m_grhss m) || not (null guards) then go ms else pure fallback
          body <- grhss g sc (m_grhss m) rest
          let guarded = case guards of
                [] -> body
                gs -> "(if " ++ intercalate " && " gs ++ " then " ++ body ++ " else " ++ rest ++ ")"
          more <- armsOf (rows ++ [row]) ms
          -- A variable pattern named as its discriminant binds nothing new.
          let texts = [if pText p' == v then "_" else pText p' | (p', v) <- zip ps vs]
          pure ((row, intercalate ", " texts, guarded) : more)

grhss :: G -> Scope -> GRHSs GhcRn (LHsExpr GhcRn) -> String -> X String
grhss g sc (GRHSs _ gs binds) rest = localBinds g sc {sExtra = []} binds (guardsChain g sc gs rest)

guardsChain :: G -> Scope -> [LGRHS GhcRn (LHsExpr GhcRn)] -> String -> X String
guardsChain g sc gs0 rest = go gs0
  where
    go [] = pure rest
    go (L _ (GRHS _ stmts body) : more) = do
      next <- go more
      stmtsChain g sc {sExtra = []} stmts (exprApplied g sc {sExtra = []} body (sExtra sc)) next

-- Guard statements in order; `next` when one fails.
stmtsChain :: G -> Scope -> [GuardLStmt GhcRn] -> X String -> String -> X String
stmtsChain g sc stmts0 body next = go stmts0
  where
    go [] = body
    go (L l s : ss) = case s of
      BodyStmt _ c _ _ -> do
        c' <- expr g sc c
        rest <- go ss
        pure $ if c' == "true" then rest else "(if " ++ c' ++ " then " ++ rest ++ " else " ++ next ++ ")"
      BindStmt _ p e -> do
        e' <- expr g sc e
        p' <- pat g p
        rest <- go ss
        let rest' = case pGuards p' of
              [] -> rest
              gs -> "(if " ++ intercalate " && " gs ++ " then " ++ rest ++ " else " ++ next ++ ")"
        pure $
          if not (exhaustive [[pTree p']] 1)
            then "(match " ++ e' ++ " with\n  | " ++ pText p' ++ " => " ++ rest' ++ "\n  | _ => " ++ next ++ ")"
            else "(match " ++ e' ++ " with\n  | " ++ pText p' ++ " => " ++ rest' ++ ")"
      LetStmt _ binds -> localBinds g sc binds (go ss)
      _ -> bad (locA l) "this guard"

-- Local bindings: functions are lifted (already registered); values become
-- lets in GHC's dependency order.
localBinds :: G -> Scope -> HsLocalBinds GhcRn -> X String -> X String
localBinds g sc binds body = case binds of
  EmptyLocalBinds _ -> body
  HsValBinds _ (XValBindsLR (NValBinds groups _)) -> do
    -- Each binding wraps the rest of the expression.
    lets <- fmap concat $ forM groups $ \(rec, bs) -> fmap concat $ forM (bagToList bs) $ \(L l b) -> case b of
      FunBind {fun_id = L _ n}
        | M.member (nkey n) (gDefs g) -> pure []
        | rec == Recursive -> bad (locA l) "a recursive local value"
        | otherwise -> do
            ty <- maybe (pure Nothing) (fmap Just . leanType g) (binderType g n)
            rhs <- matchGroup g sc [] (fun_matches b) "hsUndefined"
            pure [\rest -> "let " ++ sanitize (occ n) ++ maybe "" (" : " ++) ty ++ " := " ++ rhs ++ ";\n" ++ rest]
      PatBind {pat_lhs = p, pat_rhs = rhs}
        | rec == Recursive -> bad (locA l) "a recursive local value"
        | otherwise -> do
            p' <- pat g p
            unless (null (pGuards p') && not (pRefutable p')) (bad (locA l) "a refutable pattern binding")
            rhs' <- grhss g sc rhs "hsUndefined"
            if gEquationHere g
              then do
                -- The hints ask for the equation of the value, for Lean's
                -- termination checker: the same value, matched.
                h <- fresh g
                pure [\rest -> "match h" ++ h ++ " : " ++ rhs' ++ " with\n  | " ++ pText p' ++ " => (" ++ rest ++ ")"]
              else pure [\rest -> "let " ++ pText p' ++ " := " ++ rhs' ++ ";\n" ++ rest]
      _ -> bad (locA l) "this local binding"
    b <- body
    pure ("(" ++ foldr ($) b lets ++ ")")
  _ -> badN "implicit parameters"

-- List comprehensions ---------------------------------------------------------------

listComp :: G -> Scope -> [ExprLStmt GhcRn] -> X String
listComp g sc = go
  where
    go [] = badN "an empty list comprehension"
    go [L _ (LastStmt _ e _ _)] = do
      e' <- expr g sc e
      pure ("[" ++ e' ++ "]")
    go (L l s : ss) = case s of
      BindStmt _ p e -> do
        e' <- expr g sc e
        p' <- pat g p
        rest <- go ss
        v <- fresh g
        let inner = case pGuards p' of
              [] -> rest
              gs -> "(if " ++ intercalate " && " gs ++ " then " ++ rest ++ " else [])"
            body
              | not (exhaustive [[pTree p']] 1) = "(match " ++ v ++ " with\n  | " ++ pText p' ++ " => " ++ inner ++ "\n  | _ => [])"
              | otherwise = "(match " ++ v ++ " with\n  | " ++ pText p' ++ " => " ++ inner ++ ")"
        pure (app "HsList.concatMap" ["(fun " ++ v ++ " => " ++ body ++ ")", e'])
      BodyStmt _ c _ _ -> do
        c' <- expr g sc c
        rest <- go ss
        pure ("(if " ++ c' ++ " then " ++ rest ++ " else [])")
      LetStmt _ binds -> localBinds g sc binds (go ss)
      _ -> bad (locA l) "this statement of a list comprehension"

-- Do-blocks --------------------------------------------------------------------------

doBlock :: G -> Scope -> SrcSpan -> String -> [ExprLStmt GhcRn] -> X String
doBlock g sc sp monad stmts = do
  (bindF, thenF) <- case monad of
    m | m == tMaybe -> pure ("HsMaybe.bind", Nothing)
    m | m == tEither -> pure ("HsEither.bind", Nothing)
    m -> case (M.lookup (m, ">>=") (gInstances g), M.lookup (m, "fmap") (gInstances g), M.lookup (m, "<*>") (gInstances g)) of
      (Just b, Just f, Just a) -> pure (b, Just (f, a))
      _ -> bad sp ("a do-block in the monad " ++ m)
  let go [] = bad sp "an empty do-block"
      go [L _ (LastStmt _ e _ _)] = expr g sc e
      go [L _ (BodyStmt _ e _ _)] = expr g sc e
      go (L l s : ss) = case s of
        BindStmt _ p e -> do
          e' <- expr g sc e
          p' <- pat g p
          when (pRefutable p' || not (null (pGuards p'))) (bad (locA l) "a refutable pattern in a do-block")
          rest <- go ss
          v <- fresh g
          pure (app bindF [e', "(fun " ++ v ++ " => match " ++ v ++ " with | " ++ pText p' ++ " => " ++ rest ++ ")"])
        BodyStmt _ e _ _ -> do
          e' <- expr g sc e
          rest <- go ss
          pure (thenE bindF thenF e' rest)
        LetStmt _ binds -> localBinds g sc binds (go ss)
        _ -> bad (locA l) "this statement of a do-block"
  go stmts
  where
    -- base's default (>>) is (*>), whose default is (id <$ a) <*> b, and
    -- (<$) is fmap . const.
    thenE bindF Nothing a b = app bindF [a, "(fun _ => " ++ b ++ ")"]
    thenE _ (Just (f, ap)) a b = app ap [app f ["(HsBase.const HsBase.id)", a], b]

-- Collecting definitions ----------------------------------------------------------

-- Generic: every Name inside (variables, constructors, operators).
namesIn :: Data a => a -> [Name]
namesIn x = case cast x of
  Just (n :: Name) -> [n]
  Nothing -> concat (gmapQ namesIn x)

-- The local function bindings (with at least one argument, or of a function
-- type, or recursive) inside a binding, with their bindings; with g0Lift,
-- the local value bindings too (the hints' `lift`).
localFunctions :: Data a => G0 -> a -> [(Name, HsBind GhcRn, SrcSpan)]
localFunctions g0 x = case cast x of
  Just (HsValBinds _ (XValBindsLR (NValBinds groups _)) :: HsLocalBinds GhcRn) ->
    concat [[(n, b, locA l) | L l b@FunBind {fun_id = L _ n} <- bagToList bs, liftable g0 rec n b] | (rec, bs) <- groups]
      ++ concat (gmapQ (localFunctions g0) x)
  _ -> concat (gmapQ (localFunctions g0) x)

data G0 = G0 {g0Types :: M.Map Int Type, g0Lift :: Bool}

liftable :: G0 -> RecFlag -> Name -> HsBind GhcRn -> Bool
liftable g0 rec n b =
  g0Lift g0
    || rec == Recursive
    || any (\(L _ m) -> not (null (m_pats m))) (unLoc (mg_alts (fun_matches b)))
    || maybe False isFunOrForall (M.lookup (nkey n) (g0Types g0))
  where
    isFunOrForall t = case splitForAllTyCoVars (expandTypeSynonyms t) of
      ([], b') -> isJust (splitFunTy_maybe b')
      _ -> True

-- The names bound inside a syntax tree (patterns and bindings).
boundNames :: Data a => a -> NameList
boundNames x = NameList (go x)
  where
    go :: Data b => b -> [Name]
    go y = case cast y of
      Just (VarPat _ (L _ n) :: Pat GhcRn) -> n : concat (gmapQ go y)
      Just (AsPat _ (L _ n) _ :: Pat GhcRn) -> n : concat (gmapQ go y)
      _ -> case cast y of
        Just (FunBind {fun_id = L _ n} :: HsBind GhcRn) -> n : concat (gmapQ go y)
        _ -> concat (gmapQ go y)

newtype NameList = NameList [Name]

unNames :: NameList -> [Name]
unNames (NameList ns) = ns

-- Bound variables of patterns inside a syntax tree.
boundIn :: Data a => a -> S.Set Int
boundIn x = case cast x of
  Just (VarPat _ (L _ n) :: Pat GhcRn) -> S.insert (nkey n) (S.unions (gmapQ boundIn x))
  Just (AsPat _ (L _ n) _ :: Pat GhcRn) -> S.insert (nkey n) (S.unions (gmapQ boundIn x))
  _ -> case cast x of
    Just (FunBind {fun_id = L _ n} :: HsBind GhcRn) -> S.insert (nkey n) (S.unions (gmapQ boundIn x))
    _ -> S.unions (gmapQ boundIn x)

-- Collect generically the binder types and expression types of the
-- typechecked tree.
collectTc :: Data a => a -> ([(Int, Type)], [(RealSrcSpan, LHsExpr GhcTc)])
collectTc x = case cast x of
  Just (v :: Var) -> ([(nkey (varName v), varType v)], [])
  Nothing -> case cast x of
    Just (le@(L l _) :: LHsExpr GhcTc) ->
      let (a, b) = unzip' (gmapQ collectTc x)
       in case locA l of
            RealSrcSpan r _ -> (a, (r, le) : b)
            _ -> (a, b)
    Nothing -> unzip' (gmapQ collectTc x)
  where
    unzip' rs = (concatMap fst rs, concatMap snd rs)

-- Data types --------------------------------------------------------------------

emitTypes :: G -> X [String]
emitTypes g = do
  let loop seen = do
        tcs <- io (readIORef (gTyCons g))
        let new = [tc | (k, tc) <- M.toList tcs, not (S.member k seen)]
        if null new
          then pure seen
          else do
            forM_' new $ \tc -> forM_' (tyConDataCons tc) $ \dc -> mapM_ (leanType g . scaledThing) (dataConOrigArgTys dc)
            loop (S.union seen (S.fromList [qual (tyConName tc) | tc <- new]))
  _ <- loop S.empty
  tcs <- io (readIORef (gTyCons g))
  -- Dependency order: mutual groups.
  let deps tc = nub [k | dc <- tyConDataCons tc, t <- map scaledThing (dataConOrigArgTys dc), k <- tyConsOf t, M.member k tcs]
      sccs = stronglyConnComp [(tc, qual (tyConName tc), deps tc) | tc <- M.elems tcs]
  fmap concat $ forM sccs $ \scc -> do
    let group = case scc of
          AcyclicSCC tc -> [tc]
          CyclicSCC ts -> ts
    decls <- forM group $ \tc -> do
      let tname = sanitize (occ (tyConName tc))
          params = [tyVarLean (tyVarName v) | v <- tyConTyVars tc]
          header = unwords (tname : ["(" ++ p ++ " : Type)" | p <- params])
          self = if null params then tname else "(" ++ unwords (tname : params) ++ ")"
      cons <- forM (tyConDataCons tc) $ \dc -> do
        args <- mapM (leanType g . scaledThing) (dataConOrigArgTys dc)
        pure ("  | " ++ sanitize (occ (dataConName dc)) ++ " : " ++ concatMap (++ " → ") args ++ self)
      pure ("inductive " ++ header ++ " where\n" ++ unlines cons)
    let eqs = [tc | tc <- group, S.member (qual (tyConName tc)) (gEqTypes g)]
        names = [sanitize (occ (tyConName tc)) | tc <- group]
        inh = "deriving instance Inhabited for " ++ intercalate ", " names
        beq = ["deriving instance BEq, Repr for " ++ intercalate ", " [sanitize (occ (tyConName tc)) | tc <- eqs] | not (null eqs)]
          -- Haskell's derived Ord and Lean's both compare the constructors in
          -- their order, then the fields from left to right (rule H11).
          ++ ["deriving instance Ord for " ++ intercalate ", " [sanitize (occ (tyConName tc)) | tc <- ords] | not (null ords)]
        ords = [tc | tc <- group, S.member (qual (tyConName tc)) (gOrdTypes g)]
    accessors <- fmap concat $ forM group $ \tc -> fmap concat $ forM (tyConDataCons tc) $ \dc -> do
      let fs = map (occ . flSelector) (dataConFieldLabels dc)
          tname = sanitize (occ (tyConName tc))
          params = [tyVarLean (tyVarName v) | v <- tyConTyVars tc]
          self = let q = gNamespace g ++ "." ++ tname in if null params then q else "(" ++ unwords (q : params) ++ ")"
          implicit = concat ["{" ++ p ++ " : Type} " | p <- params]
          n = length fs
      tys <- mapM (leanType g . scaledThing) (dataConOrigArgTys dc)
      when (not (null fs) && length (tyConDataCons tc) /= 1) (badN ("a record with several constructors: " ++ tname))
      pure
        [ "def " ++ tname ++ "." ++ sanitize f ++ " " ++ implicit ++ ": " ++ self ++ " → " ++ t ++ "\n  | " ++ gNamespace g ++ "." ++ tname ++ "." ++ sanitize (occ (dataConName dc)) ++ " " ++ unwords [if j == i then "x" else "_" | j <- [0 .. n - 1]] ++ " => x\n"
            ++ "theorem " ++ tname ++ "." ++ sanitize f ++ "_sizeOf " ++ implicit ++ (if null params then "" else concat ["[SizeOf " ++ p' ++ "] " | p' <- params]) ++ "(r : " ++ self ++ ") : sizeOf (" ++ tname ++ "." ++ sanitize f ++ " r) < sizeOf r := by\n  cases r; simp only [" ++ tname ++ "." ++ sanitize f ++ "]; first | omega | (simp; done) | (simp; omega)\n"
        | (i, (f, t)) <- zip [0 ..] (zip fs tys)
        ]
    let body = if length group > 1 then ["mutual\n" ++ concat decls ++ "end\n"] else decls
    pure (body ++ [inh ++ "\n"] ++ map (++ "\n") beq ++ accessors)
  where
    forM_' xs f = mapM_ f xs

tyConsOf :: Type -> [String]
tyConsOf t = case splitTyConApp_maybe (expandTypeSynonyms t) of
  Just (tc, args) -> qual (tyConName tc) : concatMap tyConsOf args
  Nothing -> case splitFunTy_maybe t of
    Just (_, _, a, r) -> tyConsOf a ++ tyConsOf r
    Nothing -> []

-- Definitions ------------------------------------------------------------------------

-- A hint names a lifted function by `@{outer.inner}`, without the line of
-- its definition, which this replaces with the Lean name.
leanNames :: G -> String -> String
leanNames g = go
  where
    go ('@' : '{' : rest) = case break (== '}') rest of
      (key, '}' : more) -> fromMaybe ("@{" ++ key ++ "}") (leanOf key) ++ go more
      _ -> "@{" ++ go rest
    go (c : rest) = c : go rest
    go [] = []
    leanOf key = case [dLean d | d <- M.elems (gDefs g), hintKeyOf (dLean d) == key] of
      [n] -> Just n
      _ -> Nothing

-- The name of a copy of a constrained local function, when it has several.
copyName :: String -> Int -> Int -> String
copyName base i k = if k == 1 then base else base ++ "'" ++ show i

-- The definitions of an SCC, once for each copy when it is a constrained group.
emitGroup :: G -> Int -> [Def] -> X [String]
emitGroup g grp ds = case [copies | d <- ds, Just (_, copies) <- [M.lookup (nkey (dName d)) (gSpecial g)]] of
  copies : _ -> fmap concat $ forM (zip [0 ..] copies) $ \(i, (_, su)) ->
    let g' = g {gSubst = Just su, gCopy = M.insert grp i (gCopy g)}
     in forM ds $ \d -> emitDef g' d {dLean = copyName (dLean d) i (length copies)}
  [] -> forM ds (emitDef g)

emitDef :: G -> Def -> X String
emitDef g1 d = do
  let n = dName d
      b = dBind d
      g = g1 {gEquationHere = S.member (hintKeyOf (dLean d)) (gEquations g1)}
  ty <- maybe (bad (dSpan d) ("no type for " ++ occ n)) pure (binderType g n)
  capTys <- forM (dCaptured d) $ \c -> do
    t <- maybe (bad (dSpan d) ("no type for the captured " ++ occ c)) pure (binderType g c)
    t' <- leanType g t
    pure ("(" ++ sanitize (occ c) ++ " : " ++ t' ++ ")")
  mg <- case b of
    FunBind {fun_matches = m} -> pure (etaExpand m)
    _ -> bad (dSpan d) "a pattern binding at the top"
  let arity = case unLoc (mg_alts mg) of
        L _ m : _ -> length (m_pats m)
        [] -> 0
      -- A definition in point-free style takes the arguments of its type,
      -- and its body is applied to them.
      total = max arity (typeArity ty)
  (tvs, args, res) <- maybe (bad (dSpan d) ("the type of " ++ occ n)) pure (splitArgs total ty)
  -- Type variables of captured variables too.
  capTvs <- pure (nub [v | c <- dCaptured d, Just t <- [M.lookup (nkey c) (gTypes g)], v <- nonDetEltsUniqSet (tyCoVarsOfType t)])
  let allTvs = nub (map tyVarName tvs ++ map varName capTvs)
  args' <- mapM (leanType g) args
  res' <- leanType g res
  named <- paramNames g mg arity
  extraVs <- mapM (const (fresh g)) (drop arity args)
  let vs = named ++ extraVs
  let grp = M.lookup (nkey n) (gFuel g)
      inGroup = maybe False ("g" `isPrefixOf`) grp
      needsFuel = isJust grp
      sc
        | inGroup = Scope {sFuel = Just "fuel", sGroup = grp, sExtra = []}
        | needsFuel = Scope {sFuel = Just "fuel₀", sGroup = Nothing, sExtra = []}
        | otherwise = Scope {sFuel = Nothing, sGroup = Nothing, sExtra = []}
  body <- matchGroup g sc {sExtra = drop arity vs} (take arity vs) mg "hsUndefined"
  let header =
        "def " ++ dLean d ++ " "
          ++ concat ["{" ++ tyVarLean v ++ " : Type} [Inhabited " ++ tyVarLean v ++ "] " | v <- allTvs]
          ++ (if needsFuel then "(fuel₀ : Nat) " else "")
          ++ unwords capTys ++ " "
          ++ unwords ["(" ++ v ++ " : " ++ t ++ ")" | (v, t) <- zip vs args']
          ++ " : " ++ res' ++ " :=\n"
      body'
        | inGroup = "  match fuel₀ with\n  | 0 => hsUndefined\n  | fuel + 1 => " ++ body
        | otherwise = "  " ++ body
  let hintKey = takeWhile (/= '_') (dLean d) ++ dropWhile (/= '_') (takeWhile (\c -> c /= '_' || True) "")
      key = if '.' `elem` dLean d then reverse (drop 1 (dropWhile (/= '_') (reverse (dLean d)))) else dLean d
      subst ('$' : c : rest) | c >= '1' && c <= '9' = (vs !! (fromEnum c - fromEnum '1')) ++ subst rest
      subst ('@' : '{' : rest) = case break (== '}') rest of
        (k, '}' : more) -> leanNames g ("@{" ++ k ++ "}") ++ subst more
        _ -> "@{" ++ subst rest
      subst (c : rest) = c : subst rest
      subst [] = []
      hint = maybe "" (\h -> subst h ++ "\n") (M.lookup key (gHints g))
  pure (hintKey `seq` header ++ body' ++ "\n" ++ hint)

-- Main ---------------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  case args of
    libdir : srcdir : file : namespace : hints : roots@(_ : _) -> run libdir srcdir file namespace hints roots
    _ -> die "usage: TranslateHaskell LIBDIR SRCDIR MODULE NAMESPACE HINTS ROOT..."

run :: FilePath -> FilePath -> FilePath -> String -> FilePath -> [String] -> IO ()
run libdir srcdir file namespace hintsFile roots = do
  hintLines <- lines <$> readFile hintsFile
  -- The hints: "fuel NAME", and "decreasing NAME" or "before NAME" followed
  -- by lines indented by two spaces (Lean text after or before the
  -- definition NAME). "--" lines are comments.
  let blocks = hintBlocks (filter (not . ("--" `isPrefixOf`)) hintLines)
      fuelNames = [w | ("fuel", w, _) <- blocks]
      equationNames = [w | ("equations", w, _) <- blocks]
      -- A function whose local values become definitions of their own, so
      -- that proofs can name them.
      liftNames = [w | ("lift", w, _) <- blocks]
      decreasing = M.fromList [(w, t) | ("decreasing", w, t) <- blocks]
      before = M.fromList [(w, t) | ("before", w, t) <- blocks]
  (renamed, others, (tcBinds, tcAll), modName, projectMods, (eqTypes, ordTypes)) <- runGhc (Just libdir) $ do
    df <- getSessionDynFlags
    _ <- setSessionDynFlags (lang_set df {importPaths = splitColons srcdir, backend = noBackend, ghcLink = NoLink} (Just GHC2021))
    t <- guessTarget file Nothing Nothing
    setTargets [t]
    ok <- load LoadAllTargets
    unless (succeeded ok) (liftIO (die "GHC did not compile the module"))
    graph <- getModuleGraph
    let summaries = mgModSummaries graph
    infos <- forM summaries $ \ms -> do
      p <- parseModule ms
      tc <- typecheckModule p
      pure (ms, tc)
    let target = [x | x@(ms, _) <- infos, ms_hspp_file ms == file || msHsFilePath ms == file]
    (_, tcm) <- case target of
      [x] -> pure x
      _ -> liftIO (die "the module is not in the module graph")
    grp <- case tm_renamed_source tcm of
      Just (hg, _, _, _, _) -> pure hg
      Nothing -> liftIO (die "GHC kept no renamed source")
    let mods = S.fromList [moduleNameString (ms_mod_name ms) | (ms, _) <- infos]
        -- Types that derive a class, by their deriving clauses in the renamed source.
        deriving' cls =
          S.fromList
            [ moduleNameString (ms_mod_name ms) ++ "." ++ occ tn
            | (ms, tc) <- infos
            , Just (hg, _, _, _, _) <- [tm_renamed_source tc]
            , tg <- hs_tyclds hg
            , L _ (DataDecl {tcdLName = L _ tn, tcdDataDefn = defn}) <- group_tyclds tg
            , L _ clause <- dd_derivs defn
            , cls `elem` words (filter (`notElem` "(),") (showPprUnsafe (deriv_clause_tys clause)))
            ]
        -- The top-level bindings of the other modules of the graph.
        otherGroups =
          [ g'
          | (ms, tc) <- infos
          , msHsFilePath ms /= msHsFilePath (pm_mod_summary (tm_parsed_module tcm))
          , Just (hg, _, _, _, _) <- [tm_renamed_source tc]
          , XValBindsLR (NValBinds gs _) <- [hs_valds hg]
          , g' <- gs
          ]
    pure
      ( grp
      , otherGroups
      , (tm_typechecked_source tcm, [tm_typechecked_source tc | (_, tc) <- infos])
      , moduleNameString (ms_mod_name (pm_mod_summary (tm_parsed_module tcm)))
      , mods
      , (deriving' "Eq", deriving' "Ord")
      )
  let (tyPairs, exprPairs) = collectTc tcAll
  let patTypes = collectNPat tcAll
  exprTypes0 <- fmap (M.fromListWith (\_ old -> old) . concat) $ forM exprPairs $ \(r, le) -> do
    res <- try (evaluate (forceType (lhsExprType le)))
    pure $ case res of
      Left (_ :: SomeException) -> []
      Right t -> [(r, t)]
  let exprTypes = M.union (M.fromList patTypes) exprTypes0
  -- Instance methods: the typechecker names them $cMETHOD.
  let dollarC = M.map (\xs -> case (nub (map fst xs), xs) of
                            ([_], (_, t) : _) -> Just t
                            _ -> Nothing)
                  (M.fromListWith (++) [(drop 2 o, [(u, t)]) | (o, u, t) <- tyNamed, "$c" `isPrefixOf` o])
      tyNamed = collectNamed tcBinds
      instMethodType n = M.lookup (occ n) dollarC
      types0 = M.fromList tyPairs
      g0 = G0 types0 False
      topGroups = case hs_valds renamed of
        XValBindsLR (NValBinds gs _) -> gs
        ValBinds {} -> []
      topBinds = [(n, b, locA l) | (_, bs) <- topGroups, L l b@FunBind {fun_id = L _ n} <- bagToList bs]
      topByOcc = M.fromList [(occ n, x) | x@(n, _, _) <- topBinds]
      -- The functions of the other project modules that the roots reach.
      otherBinds = [(n, b, locA l) | (_, bs) <- others, L l b@FunBind {fun_id = L _ n} <- bagToList bs]
      -- Instances of the module: methods by (tycon, method).
      instBinds =
        [ (cls, tyc, n, b, locA l)
        | tg <- hs_tyclds renamed
        , L _ (ClsInstD _ ClsInstDecl {cid_poly_ty = pty, cid_binds = bs}) <- group_instds tg
        , let ws = words (filter (`notElem` "()") (showPprUnsafe pty))
        , cls : tyc : _ <- [ws]
        , L l b@FunBind {fun_id = L _ n} <- bagToList bs
        ]
  -- Reachable top-level functions from the roots, and instance methods.
  rootBinds <- forM roots $ \r -> maybe (die ("no top-level function " ++ r)) pure (M.lookup r topByOcc)
  let topKeys = M.fromList [(nkey n, x) | x@(n, _, _) <- topBinds ++ otherBinds]
      reach seen [] = seen
      reach seen ((n, b, sp) : rest)
        | M.member (nkey n) seen = reach seen rest
        | otherwise =
            let next = [x | m <- namesIn b, Just x <- [M.lookup (nkey m) topKeys]]
             in reach (M.insert (nkey n) (n, b, sp) seen) (next ++ rest)
      reached0 = reach M.empty rootBinds
      usesInstances = any (\(_, b, _) -> hasDo b) (M.elems reached0)
      reached = if usesInstances then reach reached0 [(n, b, sp) | (_, _, n, b, sp) <- instBinds] else reached0
  -- Lift local functions.
  let topDefs = M.elems reached
      lifted =
        concat
          [ [(ln, lb, lsp, n) | (ln, lb, lsp) <- localFunctions g0 {g0Lift = occ n `elem` liftNames} b]
          | (n, b, _) <- topDefs
          ]
      liftedKeys = S.fromList [nkey ln | (ln, _, _, _) <- lifted]
      allBinds = [(n, b, sp, Nothing) | (n, b, sp) <- topDefs] ++ [(ln, lb, lsp, Just outer) | (ln, lb, lsp, outer) <- lifted]
      topSet = S.fromList (map nkey [n | (n, _, _) <- topDefs])
      -- Free local variables of a binding (direct).
      freeLocals b =
        let bound = boundIn b
         in nub [m | m <- namesIn b, isInternalName m, not (S.member (nkey m) bound), not (S.member (nkey m) liftedKeys), not (S.member (nkey m) topSet)]
      directCalls b = nub [nkey m | m <- namesIn b, S.member (nkey m) liftedKeys]
      liftedMap = M.fromList [(nkey ln, (ln, lb)) | (ln, lb, _, _) <- lifted]
      -- Captured variables: transitive closure through calls of lifted functions.
      capture0 = M.fromList [(nkey ln, freeLocals lb) | (ln, lb, _, _) <- lifted]
      step cap = M.mapWithKey (\k vs -> let (_, lb) = liftedMap M.! k in nub (vs ++ concat [M.findWithDefault [] c cap | c <- directCalls lb, c /= k] `minusBound` lb)) cap
      minusBound vs lb = let bound = boundIn lb in [v | v <- vs, not (S.member (nkey v) bound)]
      fixCap cap = let cap' = step cap in if M.map (map nkey) cap' == M.map (map nkey) cap then cap else fixCap cap'
      captured = fixCap capture0
      -- A function of another module is named after its module.
      leanNameOf n outer = case outer of
        Nothing
          | modOf n == modName -> sanitize (occ n)
          | otherwise -> sanitize (map (\c -> if c == '.' then '_' else c) (modOf n) ++ "_" ++ occ n)
        Just o -> leanNameOf o Nothing ++ "." ++ sanitize (occ n) ++ "_" ++ show (srcLine n)
      srcLine n = case nameSrcSpan n of
        RealSrcSpan r _ -> srcSpanStartLine r
        _ -> 0
      instLean = M.fromList [(nkey n, "inst" ++ cls ++ "_" ++ concatMap methodName (occ n) ++ "_" ++ tyc) | (cls, tyc, n, _, _) <- instBinds]
      methodName c = case c of
        '>' -> "gt"
        '=' -> "eq"
        '<' -> "lt"
        '*' -> "star"
        '$' -> "dollar"
        _ -> [c]
      defs =
        M.fromList
          [ ( nkey n
            , Def
                { dName = n
                , dLean = fromMaybe (leanNameOf n outer) (M.lookup (nkey n) instLean)
                , dInstance = M.member (nkey n) instLean
                , dBind = b
                , dCaptured = M.findWithDefault [] (nkey n) captured
                , dSpan = sp
                , dArity = case b of
                    FunBind {fun_matches = m} -> case unLoc (mg_alts (etaExpand m)) of
                      L _ eq : _ -> length (m_pats eq)
                      [] -> 0
                    _ -> 0
                }
            )
          | (n, b, sp, outer) <- allBinds
          ]
      -- Instance methods by (tycon head, method).
      instances =
        M.fromList
          [ ((modName ++ "." ++ tyc, occ n), instLean M.! nkey n)
          | (_, tyc, n, _, _) <- instBinds
          ]
      -- Call graph and SCCs over all definitions.
      callsOf b = nub [nkey m | m <- namesIn b, M.member (nkey m) defs]
      sccs = stronglyConnComp [(d, nkey (dName d), callsOf (dBind d)) | d <- M.elems defs]
      groupOf = M.fromList [(nkey (dName d), i) | (i, scc) <- zip [0 :: Int ..] sccs, d <- flattenSCC' scc]
      fuelGroups = S.fromList [groupOf M.! nkey (dName d) | d <- M.elems defs, hintKeyOf (dLean d) `elem` fuelNames]
      -- Functions with fuel: the fuel groups and everything that calls them.
      inFuel0 = S.fromList [nkey (dName d) | d <- M.elems defs, S.member (groupOf M.! nkey (dName d)) fuelGroups]
      callers = M.fromListWith (++) [(c, [nkey (dName d)]) | d <- M.elems defs, c <- callsOf (dBind d)]
      closeFuel s = let s' = S.union s (S.fromList (concat [M.findWithDefault [] k callers | k <- S.toList s])) in if s' == s then s else closeFuel s'
      withFuel = closeFuel inFuel0
      fuel =
        M.fromList
          [ (k, if S.member (groupOf M.! k) fuelGroups then "g" ++ show (groupOf M.! k) else "caller" ++ show k)
          | k <- S.toList withFuel
          ]
  -- A local function generalised with class constraints is translated once
  -- for each type it is used at outside its recursive group: the copies of a
  -- group share the substitution of the group's type variables, a use outside
  -- the group calls the copy of its type, and a use inside the group calls
  -- the copy being translated.
  types <- pure (foldr (\(_, _, n, _, _) m -> case instMethodType n of
                    Just (Just t) -> M.insert (nkey n) t m
                    _ -> M.delete (nkey n) m) types0 instBinds)
  let constrainedBody d = case M.lookup (nkey (dName d)) types of
        Just t
          | (_ : _, body) <- splitForAllTyCoVars (expandTypeSynonyms t)
          , hasConstraint body -> Just (dropConstraints body)
        _ -> Nothing
      constrainedGroups =
        M.fromListWith (++) [(groupOf M.! nkey (dName d), [(d, b)]) | d <- M.elems defs, Just b <- [constrainedBody d]]
  special <- fmap (M.fromList . concat) $ forM (M.toList constrainedGroups) $ \(grpId, members) -> do
    let inGroup sp = any (\(m, _) -> sp `isSubspanOf` dSpan m) members
        external =
          map snd $ sortOn fst
            [ (r, (body, ty))
            | (m, body) <- members
            , d' <- M.elems defs
            , sp@(RealSrcSpan r _) <- occurrences (dName m) (dBind d')
            , not (inGroup sp)
            , Just ty <- [M.lookup r exprTypes]
            ]
        defSpans = [dSpan m | (m, _) <- members]
    substs <- forM external $ \(body, u) -> case tcMatchTy body u of
      Just su -> pure su
      Nothing -> die (showPprUnsafe defSpans ++ ": unsupported: a constrained local function used at the type " ++ showPprUnsafe u)
    let copyTypes su = [substTy su body | (_, body) <- members]
        same su su' = and (zipWith eqType (copyTypes su) (copyTypes su'))
        distinct = foldl (\acc su -> if any (same su) acc then acc else acc ++ [su]) [] substs
    when (null distinct) (die (showPprUnsafe defSpans ++ ": unsupported: a constrained local function without a use outside its group"))
    pure [(nkey (dName m), (grpId, [(substTy su body, su) | su <- distinct])) | (m, body) <- members]
  -- The project types whose derived Ord is used: the keys of sortOn, and
  -- the types of their fields that derive Ord.
  let sortKeys =
        [ k
        | d <- M.elems defs
        , RealSrcSpan r _ <- occurrencesBy (\m -> occ m == "sortOn") (dBind d)
        , Just t <- [M.lookup r exprTypes]
        , Just (_, [kf], _) <- [splitArgs 1 t]
        , Just (_, _, k) <- [splitArgs 1 kf]
        ]
      ordClosure seen [] = seen
      ordClosure seen (t : ts) = case splitTyConApp_maybe (expandTypeSynonyms t) of
        Just (tc, args)
          | let k = qual (tyConName tc)
          , S.member k ordTypes
          , not (S.member k seen) ->
              ordClosure (S.insert k seen) (args ++ concatMap (map scaledThing . dataConOrigArgTys) (tyConDataCons tc) ++ ts)
          | otherwise -> ordClosure seen (args ++ ts)
        Nothing -> ordClosure seen ts
      ordUsed = ordClosure S.empty sortKeys
  tyConsRef <- newIORef M.empty
  freshRef <- newIORef 0
  usedRef <- newIORef S.empty
  let firstCopy (_, copies) = case copies of
        (t, _) : _ -> Just t
        [] -> Nothing
      defsTyped = M.map (\d -> d {dArity = max (dArity d) (maybe 0 typeArity (maybe (M.lookup (nkey (dName d)) types) firstCopy (M.lookup (nkey (dName d)) special)))}) defs
  let g =
        G
          { gTypes = types
          , gExprTypes = exprTypes
          , gCons = M.empty
          , gFields = M.empty
          , gDefs = defsTyped
          , gFuel = fuel
          , gInstances = instances
          , gProject = projectMods
          , gEqTypes = eqTypes
          , gOrdTypes = ordUsed
          , gTyCons = tyConsRef
          , gFresh = freshRef
          , gLibraryUsed = usedRef
          , gSubst = Nothing
          , gSpecial = special
          , gCopy = M.empty
          , gNamespace = namespace
          , gHints = decreasing
          , gEquations = S.fromList equationNames
          , gEquationHere = False
          , gBefore = before
          }
  -- Types: collect the type constructors of every definition's type first,
  -- so that constructors and fields are known while translating bodies.
  r0 <- runX $ do
    let gsFor d = case M.lookup (nkey (dName d)) special of
          Just (grp, copies) -> [g {gSubst = Just su, gCopy = M.singleton grp i} | (i, (_, su)) <- zip [0 ..] copies]
          Nothing -> [g]
    forM_ (M.elems defs) $ \d -> forM_ (gsFor d) $ \gd -> do
      mapM_ (\c -> maybe (pure ()) (fmap (const ()) . leanType gd) (binderType gd c)) (dCaptured d)
      maybe (pure ()) (fmap (const ()) . leanType gd) (binderType gd (dName d))
    -- Constructor and pattern types inside bodies.
    forM_ (M.elems defs) $ \d -> forM_ (namesIn (dBind d)) $ \m -> case M.lookup (nkey m) types of
      Just t | S.member (modOf m) projectMods || isInternalName m -> X (fmap (const (Right ())) (runX (leanType g t)))
      _ -> pure ()
    emitTypes g
  typeDecls <- either die pure r0
  tcs <- readIORef tyConsRef
  let cons =
        M.fromList
          [ ( qual (dataConName dc)
            , ConInfo
                { ciLean = sanitize (occ (tyConName tc)) ++ "." ++ sanitize (occ (dataConName dc))
                , ciType = sanitize (occ (tyConName tc))
                , ciArity = length (dataConOrigArgTys dc)
                , ciFields = map (occ . flSelector) (dataConFieldLabels dc)
                , ciAlone = length (tyConDataCons tc) == 1
                , ciSiblings = [(sanitize (occ (tyConName tc)) ++ "." ++ sanitize (occ (dataConName d)), length (dataConOrigArgTys d)) | d <- tyConDataCons tc]
                }
            )
          | tc <- M.elems tcs
          , dc <- tyConDataCons tc
          ]
      fields = M.fromList [(f, (ci, i)) | ci <- M.elems cons, (i, f) <- zip [0 ..] (ciFields ci)]
      g' = g {gCons = cons, gFields = fields}
  -- Definitions in dependency order, mutual groups together.
  out <- forM (zip [0 ..] sccs) $ \(grp, scc) -> do
    let ds = flattenSCC' scc
    texts <- runX (emitGroup g' grp ds) >>= either die pure
    let pre = concat [leanNames g' t ++ "\n" | d <- ds, Just t <- [M.lookup (hintKeyOf (dLean d)) before]]
    pure $ (pre ++) $
      if length texts > 1
        then "mutual\n" ++ concat texts ++ "end\n"
        else concat texts
  used <- readIORef usedRef
  putStr $
    unlines
      [ "-- Generated by verification/TranslateHaskell.hs from " ++ modName ++ ". Do not edit."
      , "-- Library functions used: " ++ unwords (S.toList used)
      , "import HsPrelude"
      , ""
      , "set_option linter.unusedVariables false"
      , "namespace " ++ namespace
      , ""
      ]
  mapM_ putStrLn typeDecls
  -- Lean's termination checker may use the field lemmas.
  let lemmas = [takeWhile (/= ' ') (drop 8 l) | d <- typeDecls, l <- lines d, "theorem " `isPrefixOf` l]
  unless (null lemmas) $ do
    putStrLn ("macro_rules | `(tactic| decreasing_trivial) => `(tactic| (simp only [" ++ intercalate ", " lemmas ++ "]; done))")
    putStrLn ("macro_rules | `(tactic| decreasing_trivial) => `(tactic| (hs_sizes [" ++ intercalate ", " lemmas ++ "]; (try simp at *); omega))")
    putStrLn ("macro_rules | `(tactic| decreasing_trivial) => `(tactic| (hs_sizes [" ++ intercalate ", " lemmas ++ "]; omega))")
    putStrLn ""
  mapM_ putStrLn out
  putStrLn ("end " ++ namespace)

-- The number of visible arguments of a type.
typeArity :: Type -> Int
typeArity t0 = go (snd (splitForAllTyCoVars (expandTypeSynonyms t0)))
  where
    go t = case splitFunTy_maybe t of
      Just (af, _, _, r) | not (isInvisibleFunArg af) -> 1 + go r
      _ -> 0

hasConstraint :: Type -> Bool
hasConstraint t = case splitFunTy_maybe t of
  Just (af, _, _, _) -> isInvisibleFunArg af
  Nothing -> False

dropConstraints :: Type -> Type
dropConstraints t = case splitFunTy_maybe t of
  Just (af, _, _, r) | isInvisibleFunArg af -> dropConstraints r
  _ -> t

-- The spans of the occurrences of a name.
occurrences :: Data a => Name -> a -> [SrcSpan]
occurrences n = occurrencesBy (== n)

occurrencesBy :: Data a => (Name -> Bool) -> a -> [SrcSpan]
occurrencesBy p x = case cast x of
  Just (HsVar _ (L l m) :: HsExpr GhcRn) | p m -> [locA l]
  _ -> concat (gmapQ (occurrencesBy p) x)

-- A definition `f = \p1 .. pn -> e` or `f = \case alts` (one equation, no
-- guards, no where) takes the lambda's arguments: `f p1 .. pn = e`, or one
-- equation per alternative. Lean's termination checker sees the arguments.
etaExpand :: MatchGroup GhcRn (LHsExpr GhcRn) -> MatchGroup GhcRn (LHsExpr GhcRn)
etaExpand mg = case unLoc (mg_alts mg) of
  [L l (Match x ctxt outer (GRHSs _ [L _ (GRHS _ [] body)] binds))]
    | all simple outer -> case strip body of
        L _ (HsLam _ LamSingle inner) | movable binds inner -> etaExpand (withBinds binds (prefix l x ctxt outer inner))
        L _ (HsLam _ LamCase inner) | movable binds inner -> withBinds binds (prefix l x ctxt outer inner)
        _ -> mg
  _ -> mg
  where
    strip (L _ (HsPar _ e)) = strip e
    strip e = e
    -- Outer arguments that are variables or wildcards can be repeated in
    -- each equation of the lambda.
    simple (L _ (VarPat {})) = True
    simple (L _ (WildPat {})) = True
    simple _ = False
    prefix _ _ _ outer inner =
      inner {mg_alts = fmap (map (fmap (\m -> m {m_pats = outer ++ m_pats m}))) (mg_alts inner)}
    -- The where-bindings move into each equation of the lambda when the
    -- equations have none and bind no name of the same spelling.
    movable binds inner = case binds of
      EmptyLocalBinds _ -> True
      _ ->
        let bound = S.fromList (map occ (unNames (boundNames binds)))
            inEqs = S.fromList (map occ (unNames (boundNames (mg_alts inner))))
            noWhere (L _ m) = case grhssLocalBinds (m_grhss m) of
              EmptyLocalBinds _ -> True
              _ -> False
         in all noWhere (unLoc (mg_alts inner)) && S.null (S.intersection bound inEqs)
    withBinds binds inner = case binds of
      EmptyLocalBinds _ -> inner
      _ -> inner {mg_alts = fmap (map (fmap (\m -> m {m_grhss = (m_grhss m) {grhssLocalBinds = binds}}))) (mg_alts inner)}

-- The types of the overloaded literal patterns, by the pattern's span.
collectNPat :: Data a => a -> [(RealSrcSpan, Type)]
collectNPat x = case cast x of
  Just (L l (NPat ty _ _ _) :: LPat GhcTc) | RealSrcSpan r _ <- locA l -> [(r, ty)]
  _ -> concat (gmapQ collectNPat x)

-- Whether a binding has a do-block.
hasDo :: Data a => a -> Bool
hasDo x = case cast x of
  Just (HsDo _ (DoExpr _) _ :: HsExpr GhcRn) -> True
  _ -> or (gmapQ hasDo x)

-- Every Var of the typechecked tree with its name and type.
collectNamed :: Data a => a -> [(String, Int, Type)]
collectNamed x = case cast x of
  Just (v :: Var) -> [(occ (varName v), nkey (varName v), varType v)]
  Nothing -> concat (gmapQ collectNamed x)

hintKeyOf :: String -> String
hintKeyOf l = if '.' `elem` l then reverse (drop 1 (dropWhile (/= '_') (reverse l))) else l

hintBlocks :: [String] -> [(String, String, String)]
hintBlocks [] = []
hintBlocks (l : ls) = case words l of
  [kind, name] ->
    let (body, rest) = span ("  " `isPrefixOf`) ls
     in (kind, name, intercalate "\n" (map (drop 2) body)) : hintBlocks rest
  [] -> hintBlocks ls
  _ -> error ("bad hint line: " ++ l)

flattenSCC' :: SCC a -> [a]
flattenSCC' = \case
  AcyclicSCC a -> [a]
  CyclicSCC as -> as

forceType :: Type -> Type
forceType t = length (showPprUnsafe t) `seq` t

forM_ :: Monad m => [a] -> (a -> m b) -> m ()
forM_ xs f = mapM_ f xs

-- Source directories separated by colons.
splitColons :: String -> [String]
splitColons s = case break (== ':') s of
  (d, _ : rest) -> d : splitColons rest
  (d, []) -> [d]
