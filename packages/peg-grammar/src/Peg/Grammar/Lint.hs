{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The linter of the @.hpeg@ notation (ADR 0033).
--
-- The rules are fixed: they cannot be chosen, extended or silenced. Each
-- rule warns only about what follows from the meaning of the grammar, so a
-- warning always points at a real problem that a mechanical change of the
-- grammar removes. Where a rule cannot decide, it does not warn.
--
-- The rules are:
--
-- [@unreachable-alternative@] An alternative that is never tried, because
--   an earlier one always succeeds, or that never succeeds, because an
--   earlier one matches a literal that is its prefix.
-- [@duplicate-alternative@] An alternative that is the same as an earlier
--   one.
-- [@ineffective-label@] A label inside a lookahead, whose throw is a
--   failure of the lookahead (ADR 0021).
-- [@unused-binding@] A binding that no code reads. Not reported in a
--   grammar with @%syntax@, where a binding labels the children of the
--   syntax tree.
--
-- Besides the warnings, the linter gives infos (ADR 0063, ADR 0067): ways
-- to make the grammar simpler that are not wrong to leave. An info does not
-- make @peg-hs lint@ fail, and is shown only with @--verbose@. Like the
-- warnings, infos cannot be chosen or silenced. The rules of infos are:
--
-- [@omittable-unit-action@] An action @{ () }@ that can be omitted: the
--   rule has type @()@ and the alternative has no value other than unit
--   ('Peg.Grammar.Check.omitsUnitAction'). In a template, every instance
--   must allow the omission.
-- [@omittable-identity-action@] An action whose code is only the name of
--   a binding of its alternative, such as @e:Expr { e }@, where the
--   alternative without the binding and the action returns the same value
--   (ADR 0065): no predicate or argument of the alternative uses the
--   name, and without the binding the alternative counts that element
--   alone ('Peg.Grammar.Check.countedItems'). Not reported in a grammar
--   with @%syntax@, where removing a binding removes an accessor. In a
--   template, every instance must count that element alone.
-- [@omittable-unit-annotation@] A type annotation @()@ of a rule without
--   parameters or template parameters, which a rule without a type
--   annotation has (ADR 0066).
--
-- 'lintGrammar' takes a grammar that passed the checks of "Peg.Grammar"
-- (see the example there), before template expansion, and
-- 'renderLintWarning' writes the warnings in the form of @peg-hs lint@:
--
-- @
-- mapM_ (TIO.putStrLn . renderLintWarning \"Calc.hpeg\") (lintGrammar g0)
-- @
module Peg.Grammar.Lint
  ( LintWarning (..)
  , LintLevel (..)
  , lintGrammar
  , renderLintWarning
  ) where

import Data.Char (isSpace)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Check (countedItems, omitsUnitAction, unitRules)
import Peg.Grammar.Templates (expandTemplates)

-- | A warning or an info of the linter, located at the alternative, label,
-- binding or action it is about.
data LintWarning = LintWarning
  { lintLoc :: Loc
  , lintRule :: Text
  -- ^ The name of the rule of the linter, such as @unused-binding@.
  , lintMessage :: Text
  , lintHint :: Text
  -- ^ How to change the grammar.
  , lintLevel :: LintLevel
  -- ^ Whether it is a warning or an info.
  }
  deriving (Eq, Show)

-- | The level of a result of the linter (ADR 0063, ADR 0067).
data LintLevel
  = -- | Something wrong with the grammar. @peg-hs lint@ fails if there is
    -- a warning.
    LevelWarning
  | -- | Something that is not wrong, but that a change makes simpler.
    -- Infos do not make @peg-hs lint@ fail, and it shows them only with
    -- @--verbose@.
    LevelInfo
  deriving (Eq, Ord, Show)

-- | Render as @file:line:column: warning: message [rule]; hint@, the form
-- @peg-hs lint@ uses. An info has @info:@ in place of @warning:@.
renderLintWarning :: FilePath -> LintWarning -> Text
renderLintWarning file w =
  T.concat
    [ T.pack file, ":", T.pack (show (locLine (lintLoc w))), ":", T.pack (show (locColumn (lintLoc w)))
    , level, lintMessage w, " [", lintRule w, "]; ", lintHint w
    ]
  where
    level = case lintLevel w of
      LevelWarning -> ": warning: "
      LevelInfo -> ": info: "

-- | The warnings and infos of a grammar that passed the checks, in source
-- order. The grammar is the one parsed, before the expansion of templates.
lintGrammar :: Grammar -> [LintWarning]
lintGrammar g =
  sortOn (\w -> (lintLoc w, lintRule w)) $
    concatMap (alternativeWarnings throwing) rules
      ++ concatMap (concatMap labelWarnings . ruleAlts) rules
      ++ (if isJust (grammarSyntax g) then [] else concatMap (\r -> concatMap (bindingWarnings units (ruleName r)) (ruleAlts r)) rules)
      ++ unitActionInfos g
      ++ (if isJust (grammarSyntax g) then [] else identityActionInfos g)
      ++ concatMap unitAnnotationInfos rules
  where
    rules = grammarRules g
    units = unitRules g
    throwing = throwingRules rules

-- Omittable actions -----------------------------------------------------------------

-- The actions @{ () }@ that the rule of ADR 0063 allows to omit. The rules
-- are looked at after the expansion of templates, where the types of the
-- instances are known; an action of a template is omittable when it is in
-- every instance. The info is at the opening brace of the action.
unitActionInfos :: Grammar -> [LintWarning]
unitActionInfos g = case expandTemplates g of
  Left _ -> []
  Right expanded ->
    let rules = grammarRules expanded
        units = unitRules expanded
        found =
          M.fromListWith
            (&&)
            [ (Loc f line (col - 1), omitsUnitAction units (ruleName r) (altItems a))
            | r <- rules
            , a <- ruleAlts r
            , Just (Located (Loc f line col) code) <- [altAction a]
            , T.filter (not . isSpace) code == "()"
            ]
     in [ LintWarning l "omittable-unit-action" "the action can be omitted: the rule has type () and the alternative has no value" "remove { () }" LevelInfo
        | (l, True) <- M.toList found
        ]

-- The actions that return the value of a binding that the alternative
-- returns without the binding and the action (ADR 0065). As with
-- 'unitActionInfos', templates are looked at in every instance. The info is
-- at the opening brace of the action.
identityActionInfos :: Grammar -> [LintWarning]
identityActionInfos g = case expandTemplates g of
  Left _ -> []
  Right expanded ->
    let rules = grammarRules expanded
        units = unitRules expanded
        found =
          M.fromListWith
            (\(n, a) (_, b) -> (n, a && b))
            [ (Loc f line (col - 1), (name, identity units name (altItems a)))
            | r <- rules
            , a <- ruleAlts r
            , Just (Located (Loc f line col) code) <- [altAction a]
            , let name = T.filter (not . isSpace) code
            , any ((== Just name) . itemBind) (altItems a)
            ]
     in [ LintWarning
            l
            "omittable-identity-action"
            ("the action can be omitted: it returns the value of the binding " <> n <> ", which the alternative returns without the action")
            ("remove " <> n <> ": and { " <> n <> " }")
            LevelInfo
        | (l, (n, True)) <- M.toList found
        ]
  where
    identity units name items =
      case [i | i <- items, itemBind i == Just name] of
        [bound] ->
          let unbound = [if itemLoc i == itemLoc bound then i {itemBind = Nothing} else i | i <- items]
           in all (\i -> itemBind i == Nothing || itemLoc i == itemLoc bound) items
                && name `notElem` concatMap variables (concatMap (codesOf . itemExpr) items)
                && map itemLoc (countedItems units unbound) == [itemLoc bound]
        _ -> False

-- The type annotations () that a rule without a type annotation has (ADR
-- 0066). A rule with parameters or template parameters needs its
-- annotation to declare them. The info is at the start of the annotation.
unitAnnotationInfos :: Rule -> [LintWarning]
unitAnnotationInfos r =
  [ LintWarning
      l
      "omittable-unit-annotation"
      "the type annotation can be omitted: a rule without one has type ()"
      ("remove the line " <> ruleName r <> " :: ()")
      LevelInfo
  | Just l <- [ruleAnnotation r]
  , null (ruleParams r)
  , null (ruleTemplateParams r)
  , T.filter (not . isSpace) (unLoc (ruleType r)) == "()"
  ]

-- Unreachable alternatives --------------------------------------------------------

alternativeWarnings :: Set Text -> Rule -> [LintWarning]
alternativeWarnings throwing r = concat (zipWith later [0 :: Int ..] alts)
  where
    alts = ruleAlts r
    later i a = concat [warnAbout a b | (j, b) <- zip [0 ..] alts, j > i, not (reportedEarlier j)]
      where
        reportedEarlier j = any (\(k, c) -> k < i && unreachableBy c (alts !! j)) (zip [0 ..] alts)
    warnAbout a b = maybe [] pure (reason a b)
    unreachableBy a b = isJust (reason a b)
    reason a b
      | alwaysSucceeds throwing (altItems a) =
          Just (warning b "unreachable-alternative" ("the alternative is never tried: the alternative at " <> showLoc (altLoc a) <> " always succeeds") "remove it, or move it before the one that always succeeds")
      | [Item _ _ (ELit p _)] <- altItems a
      , Item _ _ (ELit q _) : _ <- altItems b
      , p `T.isPrefixOf` q =
          Just (warning b "unreachable-alternative" ("the alternative never succeeds: the alternative at " <> showLoc (altLoc a) <> " matches its prefix " <> quote p <> " first") "move it before the alternative that matches the prefix")
      | sameAlternative a b =
          Just (warning b "duplicate-alternative" ("the alternative never succeeds: it is the same as the alternative at " <> showLoc (altLoc a)) "remove it")
      | otherwise = Nothing
    warning b rule m h = LintWarning (altLoc b) rule m h LevelWarning
    quote p = "'" <> p <> "'"

-- Whether a sequence succeeds on every input: it consists of options and
-- repetitions of expressions that cannot throw a label.
alwaysSucceeds :: Set Text -> [Item] -> Bool
alwaysSucceeds throwing = all (succeeds . itemExpr)
  where
    succeeds = \case
      EOpt x -> not (mayThrow throwing x)
      EStar x -> not (mayThrow throwing x)
      _ -> False

-- The rules that may throw a label, directly or through the rules they
-- call. A reference to anything but a rule (a parameter of a template) and
-- a call of a template may throw.
throwingRules :: [Rule] -> Set Text
throwingRules rules = go (S.fromList [ruleName r | r <- rules, any (mayThrow S.empty) (exprs r)])
  where
    exprs r = map itemExpr (concatMap altItems (ruleAlts r))
    names = S.fromList (map ruleName rules)
    go s =
      let s' = S.fromList [ruleName r | r <- rules, S.member (ruleName r) s || any (mayThrow s) (exprs r) || any (`S.notMember` names) (concatMap refs (exprs r))]
       in if s' == s then s else go s'
    refs = \case
      ERef _ n _ -> [n]
      e -> concatMap refs (children e)

-- Whether an expression may throw, given the rules that may throw. A throw
-- inside a lookahead is a failure of the lookahead (ADR 0021).
mayThrow :: Set Text -> Expr -> Bool
mayThrow throwing = \case
  ELabel {} -> True
  ERef _ n _ -> S.member n throwing
  ETemplate {} -> True
  EAnd _ -> False
  ENot _ -> False
  e -> any (mayThrow throwing) (children e)

-- Two alternatives that match the same inputs in the same way: equal but for
-- the locations, and for the bindings when no code of the alternative can
-- read them.
sameAlternative :: Alt -> Alt -> Bool
sameAlternative a b = map (item keepBinds) (altItems a) == map (item keepBinds) (altItems b)
  where
    keepBinds = not (null (concatMap (codesOf . itemExpr) (altItems a ++ altItems b)))
    z = Loc 0 0 0
    item keep (Item _ n e) = Item z (if keep then n else Nothing) (expr keep e)
    expr keep = \case
      ERef _ n as -> ERef z n [Located z t | Located _ t <- as]
      EGroup alts -> EGroup (map (map (item keep)) alts)
      ELabel _ x n -> ELabel z (expr keep x) n
      EPred p (Located _ c) -> EPred p (Located z c)
      ETemplate _ n as vs -> ETemplate z n (map (expr keep) as) [Located z t | Located _ t <- vs]
      e -> mapChildren (expr keep) e

-- Ineffective labels ----------------------------------------------------------

-- A label whose failure reaches the nearest enclosing lookahead only through
-- sequences and the last alternatives of groups: its throw fails the
-- lookahead exactly as the failure without the label does.
labelWarnings :: Alt -> [LintWarning]
labelWarnings a = concatMap (expr False . itemExpr) (altItems a)
  where
    expr transparent = \case
      ELabel l x n ->
        [ LintWarning l "ineffective-label" ("the label " <> n <> " has no effect: its throw inside the lookahead is a failure of the lookahead") ("remove ^" <> n) LevelWarning
        | transparent
        ]
          ++ expr transparent x
      EAnd x -> expr True x
      ENot x -> expr True x
      EGroup alts ->
        concat [concatMap (expr (transparent && k == length alts) . itemExpr) is | (k, is) <- zip [1 ..] alts]
      ECapture x -> expr transparent x
      EDiscard x -> expr transparent x
      e -> concatMap (expr False) (children e)

-- Unused bindings -------------------------------------------------------------

-- With @%syntax@, a binding also names a child of the syntax tree and makes
-- an accessor (ADR 0019), so no binding of such a grammar is unused.

-- A binding whose name is not a variable of the action, the predicates or
-- the arguments of its alternative. Without an action, a binding that
-- chooses the value of the alternative (ADR 0030) is used, but for an
-- alternative of a rule of type () whose value is () (ADR 0064).
bindingWarnings :: Set Text -> Text -> Alt -> [LintWarning]
bindingWarnings units rule a = concatMap (sequenceWarnings True) [altItems a]
  where
    used = S.fromList (concatMap variables (maybe [] (pure . unLoc) (altAction a) ++ concatMap (codesOf . itemExpr) (altItems a)))
    sequenceWarnings top items =
      [ LintWarning l "unused-binding" ("the binding " <> n <> " is not used") ("remove " <> n <> ":") LevelWarning
      | (k, Item l (Just n) _) <- zip [0 :: Int ..] items
      , S.notMember n used
      , (top && (isJust (altAction a) || omitsUnitAction units rule (altItems a))) || choosesNothing k items
      ]
        ++ concatMap (nested . itemExpr) items
    nested = \case
      EGroup alts -> concatMap (sequenceWarnings False) alts
      ETemplate {} -> []
      e -> concatMap nested (children e)
    choosesNothing k items =
      let unbound = [if j == k then i {itemBind = Nothing} else i | (j, i) <- zip [0 :: Int ..] items]
          positions is = map itemLoc (countedItems units is)
       in positions items == positions unbound

-- The variables of Haskell code, read lexically (ADR 0082): a name inside
-- a string, a character or a comment does not count.
variables :: Text -> [Text]
variables = map unLoc . codeVariables (Loc 0 1 1)

-- The code of the predicates and arguments in an expression.
codesOf :: Expr -> [Text]
codesOf = \case
  EPred _ (Located _ c) -> [c]
  ERef _ _ as -> map unLoc as
  ETemplate _ _ as vs -> map unLoc vs ++ concatMap codesOf as
  e -> concatMap codesOf (children e)

-- Expressions -----------------------------------------------------------------

children :: Expr -> [Expr]
children = \case
  EGroup alts -> map itemExpr (concat alts)
  EStar x -> [x]
  EPlus x -> [x]
  EOpt x -> [x]
  EAnd x -> [x]
  ENot x -> [x]
  ECapture x -> [x]
  ELabel _ x _ -> [x]
  ETemplate _ _ as _ -> as
  EDiscard x -> [x]
  _ -> []

mapChildren :: (Expr -> Expr) -> Expr -> Expr
mapChildren f = \case
  EGroup alts -> EGroup [[i {itemExpr = f (itemExpr i)} | i <- is] | is <- alts]
  EStar x -> EStar (f x)
  EPlus x -> EPlus (f x)
  EOpt x -> EOpt (f x)
  EAnd x -> EAnd (f x)
  ENot x -> ENot (f x)
  ECapture x -> ECapture (f x)
  ELabel l x n -> ELabel l (f x) n
  ETemplate l n as vs -> ETemplate l n (map f as) vs
  EDiscard x -> EDiscard (f x)
  e -> e

showLoc :: Loc -> Text
showLoc (Loc _ l c) = T.pack (show l) <> ":" <> T.pack (show c)
