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
-- 'lintGrammar' takes a grammar that passed the checks of "Peg.Grammar"
-- (see the example there), before template expansion, and
-- 'renderLintWarning' writes the warnings in the form of @peg-hs lint@:
--
-- @
-- mapM_ (TIO.putStrLn . renderLintWarning \"Calc.hpeg\") (lintGrammar g0)
-- @
module Peg.Grammar.Lint
  ( LintWarning (..)
  , lintGrammar
  , renderLintWarning
  ) where

import Data.Char (isAlphaNum)
import Data.List (sortOn)
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Check (countedItems, unitRules)

-- | A warning of the linter, located at the alternative, label or binding
-- it is about.
data LintWarning = LintWarning
  { lintLoc :: Loc
  , lintRule :: Text
  -- ^ The name of the rule of the linter, such as @unused-binding@.
  , lintMessage :: Text
  , lintHint :: Text
  -- ^ How to change the grammar.
  }
  deriving (Eq, Show)

-- | Render as @file:line:column: warning: message [rule]; hint@, the form
-- @peg-hs lint@ uses.
renderLintWarning :: FilePath -> LintWarning -> Text
renderLintWarning file w =
  T.concat
    [ T.pack file, ":", T.pack (show (locLine (lintLoc w))), ":", T.pack (show (locColumn (lintLoc w)))
    , ": warning: ", lintMessage w, " [", lintRule w, "]; ", lintHint w
    ]

-- | The warnings of a grammar that passed the checks, in source order. The
-- grammar is the one parsed, before the expansion of templates.
lintGrammar :: Grammar -> [LintWarning]
lintGrammar g =
  sortOn (\w -> (lintLoc w, lintRule w)) $
    concatMap (alternativeWarnings throwing) rules
      ++ concatMap (concatMap labelWarnings . ruleAlts) rules
      ++ (if isJust (grammarSyntax g) then [] else concatMap (concatMap (bindingWarnings units) . ruleAlts) rules)
  where
    rules = grammarRules g
    units = unitRules rules
    throwing = throwingRules rules

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
    warning b = LintWarning (altLoc b)
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
    z = Loc 0 0
    item keep (Item _ n e) = Item z (if keep then n else Nothing) (expr keep e)
    expr keep = \case
      ERef _ n as -> ERef z n [Located z t | Located _ t <- as]
      EGroup alts -> EGroup (map (map (item keep)) alts)
      ELabel _ x n -> ELabel z (expr keep x) n
      EPred p (Located _ c) -> EPred p (Located z c)
      ETemplate _ n as -> ETemplate z n (map (expr keep) as)
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
        [ LintWarning l "ineffective-label" ("the label " <> n <> " has no effect: its throw inside the lookahead is a failure of the lookahead") ("remove ^" <> n)
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

-- A binding whose name is not an identifier of the action, the predicates
-- or the arguments of its alternative. Without an action, a binding that
-- chooses the value of the alternative (ADR 0030) is used.
bindingWarnings :: Set Text -> Alt -> [LintWarning]
bindingWarnings units a = concatMap (sequenceWarnings True) [altItems a]
  where
    used = S.fromList (concatMap identifiers (maybe [] (pure . unLoc) (altAction a) ++ concatMap (codesOf . itemExpr) (altItems a)))
    sequenceWarnings top items =
      [ LintWarning l "unused-binding" ("the binding " <> n <> " is not used") ("remove " <> n <> ":")
      | (k, Item l (Just n) _) <- zip [0 :: Int ..] items
      , S.notMember n used
      , (top && isJust (altAction a)) || choosesNothing k items
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

-- The identifiers of Haskell code, and the same without the quotes around
-- them. A name inside a string or a comment counts: the linter does not warn
-- when it cannot tell.
identifiers :: Text -> [Text]
identifiers code = concat [[t, T.dropAround (== '\'') t] | t <- T.split (not . identChar) code, not (T.null t)]
  where
    identChar c = isAlphaNum c || c == '_' || c == '\''

-- The code of the predicates and arguments in an expression.
codesOf :: Expr -> [Text]
codesOf = \case
  EPred _ (Located _ c) -> [c]
  ERef _ _ as -> map unLoc as
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
  ETemplate _ _ as -> as
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
  ETemplate l n as -> ETemplate l n (map f as)
  EDiscard x -> EDiscard (f x)
  e -> e

showLoc :: Loc -> Text
showLoc (Loc l c) = T.pack (show l) <> ":" <> T.pack (show c)
