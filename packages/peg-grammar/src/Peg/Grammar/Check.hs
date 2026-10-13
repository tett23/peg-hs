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
-- about the labels that may not be (ADR 0028). 'hasValue', 'countedItems' and 'unitRules' decide
-- which expressions have values (ADR 0030), and are shared with the code
-- generator and the linter.
module Peg.Grammar.Check
  ( Analysis (..)
  , check
  , hasValue
  , countedItems
  , unitRules
  ) where

import Data.Char (isSpace)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar

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
  }
  deriving (Eq, Show)

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
    significant = [i | i <- valued, isJustBind i || not (isUnit units (itemExpr i))]
    isJustBind i = maybe False (const True) (itemBind i)

-- Whether the value of an expression is made of @()@ only.
isUnit :: Set Text -> Expr -> Bool
isUnit units = \case
  ERef _ n _ -> S.member n units
  EStar x -> isUnit units x
  EPlus x -> isUnit units x
  EOpt x -> isUnit units x
  ELabel _ x _ -> isUnit units x
  EGroup alts -> not (null alts) && all (\is -> all (isUnit units . itemExpr) (countedItems units is)) alts && hasValue units (EGroup alts)
  _ -> False

-- | The rules whose type annotation is @()@, ignoring spaces (ADR 0030).
unitRules :: [Rule] -> Set Text
unitRules rules = S.fromList [ruleName r | r <- rules, T.filter (not . isSpace) (unLoc (ruleType r)) == "()"]

-- | Check a grammar whose templates have been expanded. The errors are
-- sorted by location.
check :: Grammar -> Either [Diagnostic] Analysis
check g = case grammarRules g of
  [] -> Left [Diagnostic (Loc 1 1) "the grammar has no rules"]
  firstRule : _ -> checkRules g firstRule

checkRules :: Grammar -> Rule -> Either [Diagnostic] Analysis
checkRules g firstRule =
  case sortOn diagLoc errors of
    [] -> Right (Analysis start lr nullable units)
    es -> Left es
  where
    rules = grammarRules g
    ruleMap = M.fromList [(ruleName r, r) | r <- rules]
    start = maybe (ruleName firstRule) unLoc (grammarStart g)
    nullable = nullableRules rules
    lr = leftRecursiveRules nullable rules
    units = unitRules rules
    errors =
      undefinedErrors
        ++ arityErrors
        ++ entryErrors
        ++ reachabilityErrors
        ++ concatMap (repetitionErrors nullable) rules
        ++ concatMap (altErrors units) rules
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
  ETemplate _ _ args -> concatMap exprLabels args
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
  ETemplate _ _ args -> concatMap exprRefs args
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

altErrors :: Set Text -> Rule -> [Diagnostic]
altErrors units r = concatMap alt (ruleAlts r)
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
      Nothing -> case length (countedItems units (altItems a)) of
        1 -> []
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
