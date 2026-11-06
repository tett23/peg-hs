{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Static checks and analyses of a grammar.
--
-- 'check' is the check that decides whether code can be generated from a
-- grammar: undefined rules, wrong numbers of arguments, unreachable rules,
-- repetitions of expressions that can match the empty string, bindings and
-- alternatives without a value, rules that take parameters in left
-- recursion, names reserved for generated code, and the consistency of the
-- directives. On success it returns the t'Analysis' that the code generator
-- needs. It takes a grammar whose templates have been expanded by
-- 'Peg.Grammar.Templates.expandTemplates'.
--
-- @
-- case expandTemplates g0 >>= check of
--   Left diags -> mapM_ (TIO.putStrLn . renderDiagnostic file) (templateNotes g0 diags)
--   Right analysis -> print (analysisLeftRecursive analysis)
-- @
--
-- 'check' checks that labels named in @%recover@ and @%safe@ exist, but
-- not whether a label is safe; 'Peg.Grammar.Labels.labelWarnings' warns
-- about the labels that may not be (ADR 0028). 'hasValue', 'countedItems' and 'unitRules',
-- from "Peg.Grammar.Types", decide which expressions have values (ADR 0030)
-- and which rules have type @()@ (ADR 0075), 'omitsUnitAction' which
-- alternatives of rules of type @()@ may omit their actions (ADR 0063), and
-- 'discardingRules' and 'discardsValues' which alternatives have value @()@
-- whatever their elements (ADR 0068). They are shared with the code
-- generator and the linter.
--
-- 'check' also checks the constructor names of the rules whose types are
-- generated (ADR 0075): a name is written only in such a rule, starts with
-- an upper case letter, and is not the name of another constructor or of
-- another generated type.
module Peg.Grammar.Check
  ( Analysis (..)
  , check
  , hasValue
  , countedItems
  , unitRules
  , omitsUnitAction
  , discardingRules
  , discardsValues
  ) where

import Data.Char (isUpper)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Types

-- | What the code generator needs to know about a valid grammar.
data Analysis = Analysis
  { analysisStart :: Text
  -- ^ The start rule.
  , analysisLeftRecursive :: Set Text
  -- ^ Rules that take part in left recursion.
  , analysisNullable :: Set Text
  -- ^ Rules that can succeed without consuming input.
  , analysisUnit :: Set Text
  -- ^ Rules whose type is @()@ (ADR 0030).
  , analysisTypes :: Classification
  -- ^ The types of the rules (ADR 0075).
  }
  deriving (Eq, Show)

-- | Whether an alternative of a rule may omit its action because the rule
-- has type @()@ (ADR 0063): the rule is one of the given rules of type
-- @()@, the alternative has an element, and no element it counts has a
-- value other than unit. The value of such an alternative is always @()@,
-- even when it counts one element, whose value may be @[()]@ or
-- @Maybe ()@ (ADR 0064). The action of the alternative, if any, is not
-- looked at.
omitsUnitAction :: Set Text -> Text -> [Item] -> Bool
omitsUnitAction units rule items =
  S.member rule units && not (null items) && all (isUnit units . itemExpr) (countedItems units items)

-- | The rules whose alternatives without an action have value @()@
-- whatever their elements (ADR 0068): in a grammar with @%syntax@, the
-- rules without a type annotation. Empty in a grammar without @%syntax@.
discardingRules :: Grammar -> Set Text
discardingRules g = case grammarSyntax g of
  Nothing -> S.empty
  Just _ -> S.fromList [ruleName r | r <- grammarRules g, ruleAnnotation r == Nothing]

-- | Whether an alternative without an action of a rule has value @()@
-- whatever its elements, given the 'discardingRules' (ADR 0068): the rule
-- is one of them and the alternative has an element. Its elements discard
-- their values, and the bound ones stay bound.
discardsValues :: Set Text -> Text -> [Item] -> Bool
discardsValues discarding rule items = S.member rule discarding && not (null items)

-- | Check a grammar whose templates have been expanded. The errors are
-- sorted by location.
check :: Grammar -> Either [Diagnostic] Analysis
check g = case grammarRules g of
  [] -> Left [Diagnostic (Loc 1 1) "the grammar has no rules"]
  firstRule : _ -> checkRules g firstRule

checkRules :: Grammar -> Rule -> Either [Diagnostic] Analysis
checkRules g firstRule =
  case sortOn diagLoc errors of
    [] -> Right (Analysis start lr nullable units classes)
    es -> Left es
  where
    rules = grammarRules g
    ruleMap = M.fromList [(ruleName r, r) | r <- rules]
    start = maybe (ruleName firstRule) unLoc (grammarStart g)
    nullable = nullableRules rules
    lr = leftRecursiveRules nullable rules
    classes = classify g
    units = classUnits classes
    errors =
      undefinedErrors
        ++ arityErrors
        ++ entryErrors
        ++ reachabilityErrors
        ++ concatMap (repetitionErrors nullable) rules
        ++ concatMap (altErrors units (discardingRules g) (valuedRules g classes)) rules
        ++ constructorErrors g classes
        ++ paramLrErrors
        ++ syntaxNameErrors g
        ++ concatMap hygieneErrors (grammarVerbatim g)
        ++ languageErrors
        ++ nomemoErrors
        ++ syntaxErrors
        ++ recoverErrors

    refs = [(l, n, length args) | r <- rules, a <- ruleAlts r, (l, n, args) <- itemsRefs (altItems a)]

    undefinedErrors =
      [Diagnostic l ("undefined rule " <> n) | (l, n, _) <- refs, not (M.member n ruleMap)]
        ++ [ Diagnostic l ("undefined rule " <> n)
           | Located l n <-
               maybe [] pure (grammarStart g)
                 ++ grammarEntries g
                 ++ grammarNoMemo g
                 ++ grammarTokens g
                 ++ grammarTrivia g
                 ++ grammarInline g
           , not (M.member n ruleMap)
           ]

    arityErrors =
      [ Diagnostic l msg
      | (l, n, k) <- refs
      , Just r <- [M.lookup n ruleMap]
      , let expected = length (ruleParams r)
      , k /= expected
      , let msg
              | expected == 0 = "rule " <> n <> " takes no arguments"
              | otherwise = "rule " <> n <> " expects " <> showT expected <> " argument(s), but got " <> showT k
      ]

    entryErrors =
      [ Diagnostic l ("the entry rule " <> n <> " cannot take parameters")
      | Located l n <- Located startLoc start : grammarEntries g
      , Just r <- [M.lookup n ruleMap]
      , not (null (ruleParams r))
      ]
        -- Each name makes one entry point (ADR 0038).
        ++ [ Diagnostic l ("the rule " <> n <> " is named in %entry twice")
           | (k, Located l n) <- zip [0 :: Int ..] (grammarEntries g)
           , n `elem` map unLoc (take k (grammarEntries g))
           ]
    startLoc = maybe (ruleLoc firstRule) locOf (grammarStart g)

    roots = map unLoc (grammarEntries g) ++ [unLoc r | (_, r) <- grammarRecovers g]
    reachable = reach (S.fromList (start : roots)) [start] roots
    reach seen [] [] = seen
    reach seen [] (e : es) = reach seen [e] es
    reach seen (n : ns) es =
      let next =
            [ m
            | Just r <- [M.lookup n ruleMap]
            , a <- ruleAlts r
            , (_, m, _) <- itemsRefs (altItems a)
            , not (S.member m seen)
            ]
       in reach (S.union seen (S.fromList next)) (next ++ ns) es
    reachabilityErrors =
      [ Diagnostic (ruleLoc r) ("rule " <> ruleName r <> " is unreachable from the start, entry and recovery rules")
      | r <- rules
      , not (S.member (ruleName r) reachable)
      ]

    -- ADR 0016: extensions that change the meaning of the generated code.
    languageErrors =
      [ Diagnostic l ("%language " <> x <> " is not allowed: it changes the meaning of the generated code")
      | Located l x <- grammarLanguages g
      , x `elem` ["RebindableSyntax"]
      ]

    -- ADR 0021
    usedLabels = S.fromList [n | r <- rules, a <- ruleAlts r, n <- concatMap (exprLabels . itemExpr) (altItems a)]
    recoverErrors =
      [ Diagnostic l ("undefined rule " <> n)
      | (_, Located l n) <- grammarRecovers g
      , not (M.member n ruleMap)
      ]
        ++ [ Diagnostic l ("the recovery rule " <> n <> " cannot take parameters")
           | (_, Located l n) <- grammarRecovers g
           , Just r <- [M.lookup n ruleMap]
           , not (null (ruleParams r))
           ]
        ++ [ Diagnostic l ("the label " <> n <> " has more than one recovery rule")
           | (n, _ : l : _) <- M.toList (M.fromListWith (flip (++)) [(n, [l]) | (Located l n, _) <- grammarRecovers g])
           ]
        ++ [ Diagnostic l ("the label " <> n <> " does not appear in the grammar")
           | (Located l n, _) <- grammarRecovers g
           , not (S.member n usedLabels)
           ]
        -- ADR 0028
        ++ [ Diagnostic l ("the label " <> n <> " does not appear in the grammar")
           | Located l n <- grammarSafe g
           , not (S.member n usedLabels)
           ]

    -- ADR 0006, ADR 0017
    nomemoErrors =
      [ Diagnostic l ("rule " <> n <> " takes part in left recursion and must be memoised")
      | Located l n <- grammarNoMemo g
      , S.member n lr
      ]

    -- ADR 0019
    tokenNames = S.fromList (map unLoc (grammarTokens g))
    syntaxErrors =
      case grammarSyntax g of
        Nothing ->
          [ Diagnostic l ("%" <> d <> " requires %syntax")
          | (d, xs) <- [("token", grammarTokens g), ("trivia", grammarTrivia g), ("inline", grammarInline g)]
          , Located l _ <- xs
          ]
        Just _ ->
          [ Diagnostic l ("%trivia " <> n <> " must name a %token rule")
          | Located l n <- grammarTrivia g
          , not (S.member n tokenNames)
          ]
            ++ [ Diagnostic l ("rule " <> n <> " cannot be both %token and %inline")
               | Located l n <- grammarInline g
               , S.member n tokenNames
               ]
            ++ [ Diagnostic l ("the entry rule " <> n <> " cannot be %inline: the root of the syntax tree needs a kind")
               | Located l n <- grammarInline g
               , n `elem` (start : map unLoc (grammarEntries g))
               ]

    paramLrErrors =
      [ Diagnostic (ruleLoc r) ("rule " <> ruleName r <> " takes parameters and cannot take part in left recursion")
      | r <- rules
      , not (null (ruleParams r))
      , S.member (ruleName r) lr
      ]

-- Labels written in an expression.
exprLabels :: Expr -> [Text]
exprLabels = \e -> case e of
  ELabel _ x n -> n : exprLabels x
  EDiscard x -> exprLabels x
  ETemplate _ _ args _ -> concatMap exprLabels args
  EGroup alts -> concatMap (concatMap (exprLabels . itemExpr)) alts
  EStar x -> exprLabels x
  EPlus x -> exprLabels x
  EOpt x -> exprLabels x
  EAnd x -> exprLabels x
  ENot x -> exprLabels x
  ECapture x -> exprLabels x
  _ -> []

showT :: Int -> Text
showT = T.pack . show

-- References in a sequence, with their locations and argument lists.
itemsRefs :: [Item] -> [(Loc, Text, [Located Text])]
itemsRefs = concatMap (exprRefs . itemExpr)

exprRefs :: Expr -> [(Loc, Text, [Located Text])]
exprRefs = \e -> case e of
  ERef l n args -> [(l, n, args)]
  EGroup alts -> concatMap itemsRefs alts
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

-- Nullability -------------------------------------------------------------------

nullableRules :: [Rule] -> Set Text
nullableRules rules = go S.empty
  where
    go known =
      let next = S.fromList [ruleName r | r <- rules, any (seqNullable known . altItems) (ruleAlts r)]
       in if next == known then known else go next

seqNullable :: Set Text -> [Item] -> Bool
seqNullable known = all (exprNullable known . itemExpr)

exprNullable :: Set Text -> Expr -> Bool
exprNullable known = \e -> case e of
  ELit t _ -> T.null t
  EClass _ _ -> False
  EAny -> False
  ERef _ n _ -> S.member n known
  EGroup alts -> any (seqNullable known) alts
  EStar _ -> True
  EOpt _ -> True
  EPlus x -> exprNullable known x
  EAnd _ -> True
  ENot _ -> True
  EPred _ _ -> True
  ECapture x -> exprNullable known x
  ELabel _ x _ -> exprNullable known x
  EDiscard x -> exprNullable known x
  ETemplate {} -> True

repetitionErrors :: Set Text -> Rule -> [Diagnostic]
repetitionErrors known r = concatMap (seqErrs . altItems) (ruleAlts r)
  where
    seqErrs = concatMap (\i -> exprErrs (itemLoc i) (itemExpr i))
    exprErrs l e = case e of
      EStar x -> rep l x
      EPlus x -> rep l x
      EOpt x -> exprErrs l x
      EAnd x -> exprErrs l x
      ENot x -> exprErrs l x
      ECapture x -> exprErrs l x
      ELabel _ x _ -> exprErrs l x
      EDiscard x -> exprErrs l x
      EGroup alts -> concatMap seqErrs alts
      _ -> []
    rep l x
      | exprNullable known x = Diagnostic l "the repeated expression can match the empty string, which would loop forever" : exprErrs l x
      | otherwise = exprErrs l x

-- Left recursion ---------------------------------------------------------------

-- Rules that can be called at the starting position of a rule.
leftCalls :: Set Text -> [Item] -> [Text]
leftCalls known = go
  where
    go [] = []
    go (i : is) =
      let e = itemExpr i
       in exprLeftCalls e ++ (if exprNullable known e then go is else [])
    exprLeftCalls e = case e of
      ERef _ n _ -> [n]
      EGroup alts -> concatMap go alts
      EStar x -> exprLeftCalls x
      EPlus x -> exprLeftCalls x
      EOpt x -> exprLeftCalls x
      EAnd x -> exprLeftCalls x
      ENot x -> exprLeftCalls x
      ECapture x -> exprLeftCalls x
      ELabel _ x _ -> exprLeftCalls x
      EDiscard x -> exprLeftCalls x
      _ -> []

leftRecursiveRules :: Set Text -> [Rule] -> Set Text
leftRecursiveRules known rules = S.fromList (concatMap cyclic sccs)
  where
    edges r = S.toList (S.fromList (concatMap (leftCalls known . altItems) (ruleAlts r)))
    sccs = stronglyConnComp [(r, ruleName r, edges r) | r <- rules]
    cyclic (CyclicSCC rs) = map ruleName rs
    cyclic (AcyclicSCC r) = [ruleName r | ruleName r `elem` edges r]

-- Alternatives -------------------------------------------------------------------

altErrors :: Set Text -> Set Text -> Set Text -> Rule -> [Diagnostic]
altErrors units discarding valued r = concatMap alt (ruleAlts r)
  where
    alt a =
      bindingErrors (altItems a)
        ++ duplicateErrors (altItems a)
        ++ omissionErrors a
        ++ concatMap groupErrors (altItems a)
    bindingErrors items =
      [ Diagnostic (itemLoc i) msg
      | i <- items
      , Just n <- [itemBind i]
      , msg <-
          [ "the binding " <> n <> " is reserved: names starting with an underscore belong to the generator"
          | "_" `T.isPrefixOf` n
          ]
            ++ [ "cannot bind " <> n <> ": the expression has no value (capture the text with $)"
               | not (hasValue units (itemExpr i))
               ]
      ]
    duplicateErrors items =
      [ Diagnostic l ("the binding " <> n <> " is used twice in this alternative")
      | (n, _ : l : _) <- M.toList (M.fromListWith (flip (++)) [(n, [itemLoc i]) | i <- items, Just n <- [itemBind i]])
      ]
    omissionErrors a = case altAction a of
      Just _ -> []
      -- The value of an alternative of a rule whose type is inferred or
      -- generated is that of its elements (ADR 0075).
      Nothing | S.member (ruleName r) valued -> []
      Nothing -> case length (countedItems units (altItems a)) of
        1 -> []
        _ | omitsUnitAction units (ruleName r) (altItems a) -> []
        _ | discardsValues discarding (ruleName r) (altItems a) -> []
        0 -> [Diagnostic (altLoc a) "an alternative without an action must have exactly one element with a value, but it has none"]
        k -> [Diagnostic (altLoc a) ("an alternative without an action must have exactly one element with a value, but it has " <> showT k)]
    groupErrors i = exprGroupErrors (itemExpr i)
    exprGroupErrors e = case e of
      EGroup alts -> concatMap (\is -> bindingErrors is ++ concatMap groupErrors is) alts
      EStar x -> exprGroupErrors x
      EPlus x -> exprGroupErrors x
      EOpt x -> exprGroupErrors x
      EAnd x -> exprGroupErrors x
      ENot x -> exprGroupErrors x
      ECapture x -> exprGroupErrors x
      ELabel _ x _ -> exprGroupErrors x
      EDiscard x -> exprGroupErrors x
      _ -> []

-- The rules whose types are inferred or generated (ADR 0075).
valuedRules :: Grammar -> Classification -> Set Text
valuedRules g c = S.fromList [ruleName r | r <- grammarRules g, isClassified g r, not (S.member (ruleName r) (classUnits c))]

-- Constructor names ------------------------------------------------------------

-- The constructor names written where no type is generated, the names
-- that are not names of constructors, and the constructors and types of
-- the generated module with the same name (ADR 0075).
constructorErrors :: Grammar -> Classification -> [Diagnostic]
constructorErrors g c =
  [ Diagnostic l msg
  | r <- grammarRules g
  , a <- ruleAlts r
  , Just (Located l n) <- [altConstructor a]
  , Just msg <- [misplaced r n]
  ]
    ++ [ Diagnostic l ("the constructor name " <> n <> " must start with an upper case letter")
       | r <- grammarRules g
       , isGenerated (ruleName r)
       , a <- ruleAlts r
       , Just (Located l n) <- [altConstructor a]
       , not (startsUpper n)
       ]
    ++ typeNameErrors
    ++ clashes M.empty constructors
  where
    isGenerated n = case M.lookup n (classRules c) of
      Just (Generated _) -> True
      _ -> False
    misplaced r n
      | Just _ <- grammarSyntax g = Just (prefix n <> "the grammar has %syntax")
      | Just _ <- ruleAnnotation r = Just (prefix n <> "rule " <> ruleName r <> " has a type annotation")
      | any (isJust . altAction) (ruleAlts r) = Just (prefix n <> "rule " <> ruleName r <> " has an action")
      | not (isGenerated (ruleName r)) = Just (prefix n <> "rule " <> ruleName r <> " has type (): no alternative has a value other than ()")
      | otherwise = Nothing
    prefix n = "@" <> n <> " names a constructor, but "
    startsUpper n = maybe False (isUpper . fst) (T.uncons n)
    types = classDataTypes c
    -- Two rules whose types have the same name, such as expr and Expr.
    typeNameErrors =
      [ Diagnostic (ruleLocOf (dataRule d)) ("the rules " <> dataRule e <> " and " <> dataRule d <> " have the same type name " <> dataName d <> "; rename one of them")
      | (k, d) <- zip [0 :: Int ..] types
      , e : _ <- [[e | e <- take k types, dataName e == dataName d]]
      ]
    ruleLocOf n = maybe (Loc 1 1) ruleLoc (M.lookup n ruleMap)
    ruleMap = M.fromList [(ruleName r, r) | r <- grammarRules g]
    -- A type with a constructor of its name clashes as a constructor.
    typeOwners = M.fromListWith (\_ x -> x) [(dataName d, dataRule d) | d <- types, dataName d `notElem` map conName (dataConstructors d)]
    -- The constructors of a type whose name is that of an earlier type are
    -- not compared: the rules are renamed first.
    constructors = [(d, k) | (i, d) <- zip [0 :: Int ..] types, dataName d `notElem` map dataName (take i types), k <- dataConstructors d]
    -- The constructors in order; a name is reported where it is seen again,
    -- and where it is the name of the type of another rule.
    clashes _ [] = []
    clashes seen ((d, k) : rest) =
      let n = conName k
          at = maybe (conAltLoc k) id (conNameLoc k)
          again = case M.lookup n seen of
            Just owner
              | owner == dataRule d -> [Diagnostic at ("the constructor " <> n <> " is defined twice in rule " <> owner <> "; name one of the alternatives with @Name")]
              | otherwise -> [Diagnostic at ("the constructor " <> n <> " of rule " <> dataRule d <> " is also a constructor of rule " <> owner <> "; name one of the alternatives with @Name")]
            Nothing -> case M.lookup n typeOwners of
              Just owner
                | owner /= dataRule d -> [Diagnostic at ("the constructor " <> n <> " of rule " <> dataRule d <> " has the name of the type of rule " <> owner <> "; name the alternative with @Name")]
              _ -> []
       in again ++ clashes (M.insertWith (\_ x -> x) n (dataRule d) seen) rest

-- Hygiene ----------------------------------------------------------------------

-- Lexical checks that user code does not define names the generated code
-- relies on (ADR 0014).
hygieneErrors :: Located Text -> [Diagnostic]
hygieneErrors (Located (Loc l0 _) body) =
  concat (zipWith lineErrors [l0 ..] (T.lines body))
  where
    reservedName t = "peg'" `T.isPrefixOf` t || "Peg'" `T.isPrefixOf` t
    lineErrors ln line =
      let toks = T.words line
          atColumnOne = not (T.null line) && not (T.head line == ' ' || T.head line == '\t')
          defined = case toks of
            k : n : _ | k `elem` ["data", "newtype", "type", "class", "pattern"] -> Just n
            n : _ | atColumnOne -> Just (T.takeWhile (\c -> c /= '(' && c /= ':') n)
            _ -> Nothing
          alias = case toks of
            "import" : rest -> fromMaybe [] (afterAs rest)
            _ -> []
       in [ Diagnostic (Loc ln 1) ("the name " <> n <> " is reserved for generated code")
          | Just n <- [defined]
          , atColumnOne
          , reservedName n
          ]
            ++ [ Diagnostic (Loc ln 1) ("the module alias " <> a <> " is reserved for generated code")
               | a <- alias
               , a `elem` ["PegRt", "PegPrelude"]
               ]
    afterAs ws' = case dropWhile (/= "as") ws' of
      _ : a : _ -> Just [T.takeWhile (\c -> c /= '(' && c /= ' ') a]
      _ -> Nothing

-- In a grammar with @%syntax@, two rules whose nodes would have the same
-- type, such as @expr@ and @Expr@ (ADR 0053). Tokens and inline rules have
-- no nodes.
syntaxNameErrors :: Grammar -> [Diagnostic]
syntaxNameErrors g
  | Nothing <- grammarSyntax g = []
  | otherwise = go M.empty [r | r <- grammarRules g, ruleName r `notElem` noNode]
  where
    noNode = map unLoc (grammarTokens g ++ grammarInline g)
    go _ [] = []
    go seen (r : rs) =
      let t = syntaxTypeName (ruleName r)
       in case M.lookup t seen of
            Just earlier ->
              Diagnostic (ruleLoc r) ("the rules " <> earlier <> " and " <> ruleName r <> " have the same type name " <> t <> " in the syntax tree; rename one of them")
                : go seen rs
            Nothing -> go (M.insert t (ruleName r) seen) rs
