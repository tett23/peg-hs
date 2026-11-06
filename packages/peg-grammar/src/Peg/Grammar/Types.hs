{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The values of expressions and the types of rules.
--
-- 'hasValue', 'countedItems' and 'isUnit' decide which expressions have
-- values and which values are @()@ (ADR 0004, ADR 0030, ADR 0064).
-- 'classify' decides the type of every rule (ADR 0075): a rule with a
-- type annotation has the type written, and a rule without one has type
-- @()@, except in a grammar without @%syntax@, where a rule without a type
-- annotation and without actions has
--
-- * type @()@ when no alternative has an element with a value other than
--   @()@,
-- * the type of its values when every alternative has exactly one such
--   element and the types are the same ('Inferred'),
-- * otherwise a type generated for it, with a constructor for each
--   alternative ('Generated').
--
-- The rules depend on each other, so the classification is a fixed point:
-- first of the rules of type @()@, then of the inferred types. Two types
-- are the same when their texts are the same without spaces; an alias is
-- another type. A rule whose type cannot be inferred gets a generated
-- type, so a generated module never has a type error from the
-- classification.
--
-- @
-- let c = classify g
-- in [(dataName d, map conName (dataConstructors d)) | d <- classDataTypes c]
-- @
--
-- "Peg.Grammar.Check" checks the constructor names and the code generator
-- (@Peg.Codegen@ in @peg-codegen@) generates the types. Classify a grammar
-- whose templates have been expanded: a template call has no type before.
module Peg.Grammar.Types
  ( -- * Values of expressions
    hasValue
  , countedItems
  , isUnit
  , fieldItems
  , valueRefs
    -- * Types of rules
  , Classification (..)
  , RuleType (..)
  , ValueType (..)
  , DataType (..)
  , Constructor (..)
  , classify
  , isClassified
  , unitRules
  , generatedTypeName
  , defaultDeriving
    -- * Writing types
  , typeText
  , typeCode
  , typeAtom
  , sameType
  , dataTypeText
  , constructorTypeText
  ) where

import Data.Char (isSpace, isUpper, toUpper)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust, isNothing, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar

-- Values -------------------------------------------------------------------------

-- | Whether an expression produces a value that can be bound (ADR 0004),
-- given the rules whose type is @()@ (ADR 0030).
hasValue :: Set Text -> Expr -> Bool
hasValue units = \e -> case e of
  ERef {} -> True
  ECapture _ -> True
  EStar x -> hasValue units x
  EPlus x -> hasValue units x
  EOpt x -> hasValue units x
  ELabel _ x _ -> hasValue units x
  ETemplate {} -> True
  EGroup alts -> not (null alts) && all ((== 1) . length . countedItems units) alts
  _ -> False

-- | The items of a sequence whose values count, for a group's value and an
-- alternative without an action (ADR 0030): the items with a value, except
-- unbound items whose value is unit. When no item has a value other than
-- unit, the unit values count too.
countedItems :: Set Text -> [Item] -> [Item]
countedItems units items = if null significant then valued else significant
  where
    valued = [i | i <- items, hasValue units (itemExpr i)]
    significant = [i | i <- valued, isJust (itemBind i) || not (isUnit units (itemExpr i))]

-- | Whether the value of an expression is made of @()@ only, given the
-- rules whose type is @()@: a call of such a rule, its repetitions and
-- options (@[()]@, @Maybe ()@, ADR 0064), and a group of such values.
isUnit :: Set Text -> Expr -> Bool
isUnit units = \case
  ERef _ n _ -> S.member n units
  EStar x -> isUnit units x
  EPlus x -> isUnit units x
  EOpt x -> isUnit units x
  ELabel _ x _ -> isUnit units x
  EGroup alts -> not (null alts) && all (\is -> all (isUnit units . itemExpr) (countedItems units is)) alts && hasValue units (EGroup alts)
  _ -> False

-- | The items of a sequence that have a value other than @()@, bound or
-- not: the values of an alternative of a rule whose type is inferred or
-- generated (ADR 0075), and the arguments of its constructor.
fieldItems :: Set Text -> [Item] -> [Item]
fieldItems units items = [i | i <- items, hasValue units (itemExpr i), not (isUnit units (itemExpr i))]

-- Types ----------------------------------------------------------------------------

-- | The type of a value.
data ValueType
  = -- | The text of a capture.
    TText
  | -- | The value of @e*@ and @e+@.
    TList ValueType
  | -- | The value of @e?@.
    TMaybe ValueType
  | -- | A type by its text: a type annotation, or the name of a generated
    -- type.
    TNamed Text
  deriving (Eq, Ord, Show)

-- | A constructor of a generated type.
data Constructor = Constructor
  { conName :: Text
  -- ^ The name after @\@@, or the default name.
  , conNameLoc :: Maybe Loc
  -- ^ Where the name is written after @\@@; 'Nothing' for a default name.
  , conAltLoc :: Loc
  -- ^ The alternative.
  , conFields :: [ValueType]
  -- ^ The types of the values of the alternative, in order.
  }
  deriving (Eq, Show)

-- | A type generated for a rule (ADR 0075).
data DataType = DataType
  { dataRule :: Text
  -- ^ The rule whose type it is.
  , dataName :: Text
  -- ^ The name of the type ('generatedTypeName').
  , dataConstructors :: [Constructor]
  -- ^ One for each alternative, in order.
  , dataDeriving :: [Text]
  -- ^ The classes derived, as @%deriving@ writes them.
  }
  deriving (Eq, Show)

-- | The type of a rule.
data RuleType
  = -- | A type annotation, as written.
    Annotated Text
  | -- | No type annotation and the type @()@ (ADR 0066).
    UnitType
  | -- | No type annotation, no action, and the type of its values.
    Inferred ValueType
  | -- | No type annotation, no action, and a generated type.
    Generated DataType
  deriving (Eq, Show)

-- | The types of the rules of a grammar.
data Classification = Classification
  { classRules :: M.Map Text RuleType
  -- ^ The type of each rule.
  , classUnits :: Set Text
  -- ^ The rules whose type is @()@: their type annotation is @()@,
  -- ignoring spaces (ADR 0030), or they are 'UnitType'.
  , classDataTypes :: [DataType]
  -- ^ The generated types, in the order of their rules.
  , classUnknown :: Set Text
  -- ^ The undefined rules, and the rules whose types depend on a call of
  -- an undefined rule, through the values of their elements. Their types
  -- are not known; the checks that depend on the types say nothing about
  -- them, and the error is the undefined rule.
  }
  deriving (Eq, Show)

-- | The classes that a generated type derives without @%deriving@.
defaultDeriving :: [Text]
defaultDeriving = ["Eq", "Show"]

-- | The name of the type generated for a rule: the rule name with its
-- first letter made upper case. A rule name whose first letter has no
-- upper case gets @Rule'@ before it (ADR 0053).
--
-- @
-- generatedTypeName "expr" == "Expr"
-- generatedTypeName "数式" == "Rule'数式"
-- @
generatedTypeName :: Text -> Text
generatedTypeName n = case T.uncons n of
  Just (c, rest) | isUpper (toUpper c) -> T.cons (toUpper c) rest
  _ -> "Rule'" <> n

-- | Whether the type of a rule is decided by 'classify' rather than by an
-- annotation (ADR 0075): in a grammar without @%syntax@, a rule without a
-- type annotation and without actions.
isClassified :: Grammar -> Rule -> Bool
isClassified g r =
  isNothing (grammarSyntax g)
    && isNothing (ruleAnnotation r)
    && null (ruleTemplateParams r)
    && all (isNothing . altAction) (ruleAlts r)

-- | The rules whose type is @()@ ('classUnits').
unitRules :: Grammar -> Set Text
unitRules = classUnits . classify

-- The state of a rule whose type is being inferred.
data Infer = Unknown | Known ValueType | Conflict
  deriving (Eq)

-- | The types of the rules of a grammar.
classify :: Grammar -> Classification
classify g = Classification ruleTypes (S.intersection units defined) dataTypes unknown
  where
    rules = grammarRules g
    classified = [r | r <- rules, isClassified g r]
    annotatedUnit r = isJust (ruleAnnotation r) && T.filter (not . isSpace) (unLoc (ruleType r)) == "()"
    defined = S.fromList (map ruleName rules)
    -- A call of an undefined rule has no value here: "undefined rule" is
    -- its error, and it must not make its caller a rule with values.
    undefinedRules = S.fromList [n | r <- rules, a <- ruleAlts r, i <- altItems a, n <- exprRefs (itemExpr i), not (S.member n defined)]
    -- The unknown types spread to the classified rules whose values call
    -- them.
    unknown = unknownFix undefinedRules
    unknownFix known =
      let more = S.fromList [ruleName r | r <- classified, not (S.member (ruleName r) known), any (any (`S.member` known) . concatMap (valueRefs . itemExpr) . altItems) (ruleAlts r)]
       in if S.null more then known else unknownFix (S.union known more)
    fixedUnits = S.union undefinedRules (S.fromList [ruleName r | r <- rules, annotatedUnit r || (isNothing (ruleAnnotation r) && not (isClassified g r))])
    -- Stage 1: the rules of type (). A rule leaves the set when one of its
    -- alternatives has a value other than (); the set only shrinks.
    units = unitFix (S.fromList (map ruleName classified))
    unitFix unitT =
      let us = S.union fixedUnits unitT
          promoted = S.fromList [ruleName r | r <- classified, S.member (ruleName r) unitT, any (not . null . fieldItems us . altItems) (ruleAlts r)]
       in if S.null promoted then us else unitFix (S.difference unitT promoted)
    valued = [r | r <- classified, not (S.member (ruleName r) units)]
    fieldsOf r = map (fieldItems units . altItems) (ruleAlts r)
    named r = any (isJust . altConstructor) (ruleAlts r)
    -- Stage 2: a rule with an alternative whose number of values is not 1,
    -- or with a constructor name, is generated. The others are candidates.
    generated0 = S.fromList [ruleName r | r <- valued, named r || any ((/= 1) . length) (fieldsOf r)]
    annotations = M.fromList [(ruleName r, T.strip (unLoc (ruleType r))) | r <- rules, isJust (ruleAnnotation r)]
    (generated, inferred) = resolve generated0
    resolve gen =
      let types = inferFix gen
          conflicts = S.fromList [n | (n, Conflict) <- M.toList types]
          unresolved = S.fromList [n | (n, Unknown) <- M.toList types]
       in if not (S.null conflicts)
            then resolve (S.union gen conflicts)
            else
              if not (S.null unresolved)
                then resolve (S.union gen unresolved)
                else (gen, M.fromList [(n, t) | (n, Known t) <- M.toList types])
    candidatesOf gen = [r | r <- valued, not (S.member (ruleName r) gen)]
    -- The types of the candidates, from all unknown. A candidate whose
    -- values have two types is a conflict, which ends the iteration.
    inferFix gen = go (length (candidatesOf gen) + 1) (M.fromList [(ruleName r, Unknown) | r <- candidatesOf gen])
      where
        go :: Int -> M.Map Text Infer -> M.Map Text Infer
        go k st =
          let st' = M.fromList [(ruleName r, step st r) | r <- candidatesOf gen]
           in if st' == st || k <= 0 || Conflict `elem` M.elems st' then st' else go (k - 1) st'
        step st r =
          case distinct (mapMaybe (\fs -> case fs of [i] -> exprType (lookupType gen (\n -> M.lookup n st)) (itemExpr i); _ -> Nothing) (fieldsOf r)) of
            [] -> Unknown
            [t] -> Known t
            _ -> Conflict
    distinct = foldr (\t acc -> if any (sameType t) acc then acc else t : acc) [] . reverse
    -- The type of a call of a rule, given the generated rules and the
    -- state of the candidates.
    lookupType gen state n
      | Just t <- M.lookup n annotations = Just (TNamed t)
      | S.member n units = Just (TNamed "()")
      | S.member n gen = Just (TNamed (generatedTypeName n))
      | otherwise = case state n of
          Just (Known t) -> Just t
          _ -> Nothing
    finalType n = lookupType generated (\x -> Known <$> M.lookup x inferred) n
    exprType look = \case
      ERef _ n _ -> look n
      ECapture _ -> Just TText
      EStar x -> TList <$> exprType look x
      EPlus x -> TList <$> exprType look x
      EOpt x -> TMaybe <$> exprType look x
      ELabel _ x _ -> exprType look x
      EGroup alts -> do
        ts <- mapM (\is -> case countedItems units is of [i] -> exprType look (itemExpr i); _ -> Nothing) alts
        case ts of
          t : _ -> Just t
          [] -> Nothing
      _ -> Nothing
    derivedClasses = maybe defaultDeriving (map unLoc . unLoc) (grammarDeriving g)
    dataTypes = [d | r <- classified, Generated d <- [typeOf r]]
    dataTypeOf r =
      let name = generatedTypeName (ruleName r)
          alts = ruleAlts r
          one = length alts == 1
       in DataType
            { dataRule = ruleName r
            , dataName = name
            , dataConstructors =
                [ Constructor
                    { conName = maybe (if one then name else name <> T.pack (show k)) unLoc (altConstructor a)
                    , conNameLoc = locOf <$> altConstructor a
                    , conAltLoc = altLoc a
                    , conFields = [maybe (TNamed "()") id (exprType finalType (itemExpr i)) | i <- fieldItems units (altItems a)]
                    }
                | (k, a) <- zip [1 :: Int ..] alts
                ]
            , dataDeriving = derivedClasses
            }
    typeOf r
      | Just t <- M.lookup (ruleName r) annotations = Annotated t
      | S.member (ruleName r) units = UnitType
      | S.member (ruleName r) generated = Generated (dataTypeOf r)
      | Just t <- M.lookup (ruleName r) inferred = Inferred t
      | otherwise = UnitType
    ruleTypes = M.fromList [(ruleName r, typeOf r) | r <- rules]

-- | The rules whose values are part of the value of an expression: the
-- calls outside captures and lookaheads.
valueRefs :: Expr -> [Text]
valueRefs = \case
  ERef _ n _ -> [n]
  EGroup alts -> concatMap (concatMap (valueRefs . itemExpr)) alts
  EStar x -> valueRefs x
  EPlus x -> valueRefs x
  EOpt x -> valueRefs x
  ELabel _ x _ -> valueRefs x
  ETemplate _ _ args _ -> concatMap valueRefs args
  _ -> []

-- The rules that an expression calls.
exprRefs :: Expr -> [Text]
exprRefs = \case
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
  ETemplate _ _ args _ -> concatMap exprRefs args
  _ -> []

-- Writing -------------------------------------------------------------------------

-- | Whether two types are the same: their texts are the same without
-- spaces (ADR 0075).
sameType :: ValueType -> ValueType -> Bool
sameType a b = key a == key b
  where
    key = T.filter (not . isSpace) . typeText

-- | A type as the user reads it: @Text@, @[Expr]@, @Maybe Text@.
typeText :: ValueType -> Text
typeText = render "Text" "Maybe"

-- | A type as the generated module writes it, with the names of the
-- runtime and of the qualified Prelude.
typeCode :: ValueType -> Text
typeCode = render "PegRt.Text" "PegPrelude.Maybe"

render :: Text -> Text -> ValueType -> Text
render text maybe' = go
  where
    go = \case
      TText -> text
      TList t -> "[" <> go t <> "]"
      TMaybe t -> maybe' <> " " <> atom t
      TNamed t -> T.strip t
    atom t = parens (go t)

-- | A type in parentheses when it has a space outside brackets, so that
-- it can be an argument of a type or a constructor.
typeAtom :: Text -> Text
typeAtom = parens

parens :: Text -> Text
parens t
  | spaced (0 :: Int) (T.unpack t) = "(" <> t <> ")"
  | otherwise = t
  where
    spaced _ [] = False
    spaced d (c : cs)
      | c `elem` ("([" :: String) = spaced (d + 1) cs
      | c `elem` (")]" :: String) = spaced (d - 1) cs
      | isSpace c && d <= 0 = True
      | otherwise = spaced d cs

-- | The declaration of a generated type as the user reads it, with its
-- @deriving@ clause on a second line when it derives classes:
--
-- @
-- data Expr = Expr1 Expr Atom | Expr2 Atom
--   deriving (Eq, Show)
-- @
dataTypeText :: DataType -> Text
dataTypeText d =
  T.intercalate "\n" $
    [keyword <> " " <> dataName d <> " = " <> T.intercalate " | " [T.unwords (conName c : map (parens . typeText) (conFields c)) | c <- dataConstructors d]]
      ++ ["  deriving (" <> T.intercalate ", " (dataDeriving d) <> ")" | not (null (dataDeriving d))]
  where
    keyword = case dataConstructors d of
      [c] | [_] <- conFields c -> "newtype"
      _ -> "data"

-- | The type of a constructor, as @Add :: Expr -> Atom -> Expr@.
constructorTypeText :: DataType -> Constructor -> Text
constructorTypeText d c = conName c <> " :: " <> T.intercalate " -> " (map (parens . typeText) (conFields c) ++ [dataName d])
