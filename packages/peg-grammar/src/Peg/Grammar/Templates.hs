{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Expanding rule templates (ADR 0031).
--
-- A call of a template, @List<Exp, ','>@, becomes a reference to an
-- instance of the template: an ordinary rule made for each distinct list of
-- arguments, with the parameters replaced by the arguments. The grammar
-- that results has no template, and the static checks, left recursion and
-- code generation treat the instances as ordinary rules.
module Peg.Grammar.Templates
  ( expandTemplates
  , templateNotes
  ) where

import Data.Char (isAlphaNum)
import Data.List (nub)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust, mapMaybe)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar

-- | Replace the template calls of a grammar with references to instances,
-- and remove the templates. Instances are rules that cannot be named in
-- directives; in a grammar with @%syntax@, they are @%inline@.
expandTemplates :: Grammar -> Either [Diagnostic] Grammar
expandTemplates g
  | M.null templates = Right g
  | not (null directiveErrors) = Left directiveErrors
  | otherwise = case runExpand (mapM expandRule ordinary >>= \rs -> (rs ++) <$> drain) (St M.empty [] [] 0 M.empty S.empty) of
      (_, St {stErrors = errs@(_ : _)}) -> Left (nub (reverse errs))
      (rules, st) ->
        Right
          g
            { grammarRules = rules
            , grammarInline =
                grammarInline g
                  ++ [Located (ruleLoc r) (ruleName r) | isJust (grammarSyntax g), r <- rules, S.member (ruleName r) (stInstanceNames st)]
            }
  where
    templates = M.fromList [(ruleName r, r) | r <- grammarRules g, not (null (ruleTemplateParams r))]
    ordinary = [r | r <- grammarRules g, null (ruleTemplateParams r)]
    ruleTypes = M.fromList [(ruleName r, unLoc (ruleType r)) | r <- grammarRules g]
    usedNames = S.fromList (map ruleName (grammarRules g))

    directiveErrors =
      [ Diagnostic l ("the template " <> n <> " cannot be named in %" <> d)
      | (d, names) <-
          [ ("start", maybe [] pure (grammarStart g))
          , ("entry", grammarEntries g)
          , ("recover", map snd (grammarRecovers g))
          , ("nomemo", grammarNoMemo g)
          , ("token", grammarTokens g)
          , ("trivia", grammarTrivia g)
          , ("inline", grammarInline g)
          ]
      , Located l n <- names
      , M.member n templates
      ]
        ++ [ Diagnostic (ruleLoc r) ("the template " <> ruleName r <> " cannot take parameters")
           | r <- M.elems templates
           , not (null (ruleParams r))
           ]
        ++ [ Diagnostic (ruleLoc r) ("the template " <> ruleName r <> " has two parameters named " <> p)
           | r <- M.elems templates
           , let names = map templateParamName (ruleTemplateParams r)
           , p <- nub [x | x <- names, length (filter (== x) names) > 1]
           ]

    expandRule r = do
      alts <- mapM (expandAlt 0) (ruleAlts r)
      pure r {ruleAlts = alts}

    expandAlt depth a = do
      items <- mapM (expandItem depth) (altItems a)
      pure a {altItems = items}

    expandItem depth i = (\e -> i {itemExpr = e}) <$> expandExpr depth (itemExpr i)

    expandExpr depth = \case
      ERef l n args
        | M.member n templates -> do
            addError (Diagnostic l ("the template " <> n <> " needs arguments: " <> n <> "<...>"))
            pure (ERef l n args)
      ETemplate l n args -> case M.lookup n templates of
        Nothing -> do
          addError (Diagnostic l ("rule " <> n <> " is not a template"))
          pure (ERef l n [])
        Just t -> do
          args' <- mapM (expandExpr depth) args
          let params = ruleTemplateParams t
          if length args' /= length params
            then do
              addError (Diagnostic l ("the template " <> n <> " expects " <> T.pack (show (length params)) <> " argument(s), but got " <> T.pack (show (length args'))))
              pure (ERef l n [])
            else do
              tys <- mapM (argType l) (zip params args')
              name <- instanceOf l depth t args' tys
              pure (ERef l name [])
      EGroup alts -> EGroup <$> mapM (mapM (expandItem depth)) alts
      EStar x -> EStar <$> expandExpr depth x
      EPlus x -> EPlus <$> expandExpr depth x
      EOpt x -> EOpt <$> expandExpr depth x
      EAnd x -> EAnd <$> expandExpr depth x
      ENot x -> ENot <$> expandExpr depth x
      ECapture x -> ECapture <$> expandExpr depth x
      ELabel l x n -> (\x' -> ELabel l x' n) <$> expandExpr depth x
      EDiscard x -> EDiscard <$> expandExpr depth x
      e -> pure e

    -- The type of the argument of a typed parameter.
    argType l (p, a) = case templateParamType p of
      Nothing -> pure Nothing
      Just _ -> case a of
        ERef _ n _ -> do
          known <- gets' stInstanceTypes
          pure (Just (M.findWithDefault (M.findWithDefault "()" n ruleTypes) n known))
        ECapture _ -> pure (Just "PegRt.Text")
        _ -> do
          addError (Diagnostic l ("the argument for " <> templateParamName p <> " must be a rule, a capture or a template call, since its value is used"))
          pure (Just "()")

    instanceOf l depth t args tys = do
      let key = (ruleName t, show (map plain args))
      existing <- gets' (M.lookup key . stInstances)
      case existing of
        Just name -> pure name
        Nothing -> do
          n <- gets' stCount
          let name = freshName (ruleName t) n
          modify' $ \st ->
            st
              { stInstances = M.insert key name (stInstances st)
              , stPending = stPending st ++ [(name, t, args, tys, depth + 1, l)]
              , stCount = stCount st + 1
              , stInstanceTypes = M.insert name (instanceType t tys) (stInstanceTypes st)
              , stInstanceNames = S.insert name (stInstanceNames st)
              }
          pure name

    freshName base n = case [c | k <- [n ..], let c = base <> "'" <> T.pack (show (k :: Int)), not (S.member c usedNames)] of
      c : _ -> c
      [] -> base

    -- Expand the pending instances, which may add more.
    drain =
      gets' stPending >>= \case
        [] -> pure []
        (name, t, args, _, depth, l) : _ -> do
          modify' $ \st -> st {stPending = drop 1 (stPending st)}
          rule <-
            if depth > maxDepth || sum (map exprSize args) > maxSize
              then do
                addError (Diagnostic l ("the expansion of the template " <> ruleName t <> " does not end: templates call templates more than " <> T.pack (show maxDepth) <> " levels deep"))
                pure Nothing
              else do
                let sub = M.fromList (zip (map templateParamName (ruleTemplateParams t)) (zip (ruleTemplateParams t) args))
                alts <- mapM (expandAlt depth . substituteAlt sub) (ruleAlts t)
                ty <- gets' (M.findWithDefault "()" name . stInstanceTypes)
                pure (Just t {ruleName = name, ruleTemplateParams = [], ruleType = (ruleType t) {unLoc = ty}, ruleAlts = alts})
          rest <- drain
          pure (maybe rest (: rest) rule)

    maxDepth = 64
    -- Arguments can grow at each level (T<x> <- T<(x x)>), faster than the
    -- depth limit catches.
    maxSize = 10000

-- The type of an instance: the type variables of the template's type
-- replaced by the types of the arguments.
instanceType :: Rule -> [Maybe Text] -> Text
instanceType t tys = foldl replaceVar (unLoc (ruleType t)) [(v, ty) | (TemplateParam _ (Just v), Just ty) <- zip (ruleTemplateParams t) tys]
  where
    replaceVar ty (v, with) = T.concat (map (\w -> if w == v then "(" <> with <> ")" else w) (identifierSplit ty))

-- Split a type into identifiers and the text between them.
identifierSplit :: Text -> [Text]
identifierSplit t
  | T.null t = []
  | isIdent (T.head t) = let (a, b) = T.span isIdent t in a : identifierSplit b
  | otherwise = let (a, b) = T.break isIdent t in a : identifierSplit b
  where
    isIdent c = isAlphaNum c || c == '_' || c == '\''

-- Replace the parameters in the body of a template. A typed parameter's
-- value is used, so the argument is put as it is; an untyped parameter's
-- value is discarded.
substituteAlt :: M.Map Text (TemplateParam, Expr) -> Alt -> Alt
substituteAlt sub a = a {altItems = map item (altItems a)}
  where
    item i = i {itemExpr = expr (itemExpr i)}
    expr = \case
      ERef _ n [] | Just (p, arg) <- M.lookup n sub -> if isJust (templateParamType p) then arg else EDiscard arg
      EGroup alts -> EGroup (map (map item) alts)
      EStar x -> EStar (expr x)
      EPlus x -> EPlus (expr x)
      EOpt x -> EOpt (expr x)
      EAnd x -> EAnd (expr x)
      ENot x -> ENot (expr x)
      ECapture x -> ECapture (expr x)
      ELabel l x n -> ELabel l (expr x) n
      EDiscard x -> EDiscard (expr x)
      ETemplate l n args -> ETemplate l n (map expr args)
      e -> e

-- The number of nodes of an expression.
exprSize :: Expr -> Int
exprSize = \case
  EGroup alts -> 1 + sum (map (sum . map (exprSize . itemExpr)) alts)
  EStar x -> 1 + exprSize x
  EPlus x -> 1 + exprSize x
  EOpt x -> 1 + exprSize x
  EAnd x -> 1 + exprSize x
  ENot x -> 1 + exprSize x
  ECapture x -> 1 + exprSize x
  ELabel _ x _ -> 1 + exprSize x
  EDiscard x -> 1 + exprSize x
  ETemplate _ _ args -> 1 + sum (map exprSize args)
  _ -> 1

-- An expression without locations, to compare arguments.
plain :: Expr -> Expr
plain = \case
  ERef _ n args -> ERef noLoc n [Located noLoc (unLoc a) | a <- args]
  EGroup alts -> EGroup (map (map (\i -> Item noLoc (itemBind i) (plain (itemExpr i)))) alts)
  EStar x -> EStar (plain x)
  EPlus x -> EPlus (plain x)
  EOpt x -> EOpt (plain x)
  EAnd x -> EAnd (plain x)
  ENot x -> ENot (plain x)
  ECapture x -> ECapture (plain x)
  ELabel _ x n -> ELabel noLoc (plain x) n
  EPred b (Located _ c) -> EPred b (Located noLoc c)
  ETemplate _ n args -> ETemplate noLoc n (map plain args)
  EDiscard x -> EDiscard (plain x)
  e -> e
  where
    noLoc = Loc 0 0

-- | Add to the diagnostics located in the body of a template the call that
-- expanded it, and remove duplicates: an error in a template is found once
-- for each instance. The grammar is the one before expansion.
templateNotes :: Grammar -> [Diagnostic] -> [Diagnostic]
templateNotes g = nub . map note
  where
    templates = [r | r <- grammarRules g, not (null (ruleTemplateParams r))]
    firstCall = M.fromListWith (\_ old -> old) [(n, l) | r <- grammarRules g, a <- ruleAlts r, (l, n) <- concatMap (calls . itemExpr) (altItems a)]
    locsOf r = S.fromList (ruleLoc r : concat [altLoc a : concatMap itemLocs (altItems a) | a <- ruleAlts r])
    itemLocs i = itemLoc i : exprLocs (itemExpr i)
    exprLocs = \case
      ERef l _ args -> l : map locOf args
      ETemplate l _ args -> l : concatMap exprLocs args
      ELabel l x _ -> l : exprLocs x
      EGroup alts -> concatMap (concatMap itemLocs) alts
      EPred _ c -> [locOf c]
      x -> concatMap exprLocs (children x)
    children = \case
      EStar x -> [x]
      EPlus x -> [x]
      EOpt x -> [x]
      EAnd x -> [x]
      ENot x -> [x]
      ECapture x -> [x]
      EDiscard x -> [x]
      _ -> []
    calls = \case
      ETemplate l n args -> (l, n) : concatMap calls args
      EGroup alts -> concatMap (concatMap (calls . itemExpr)) alts
      ELabel _ x _ -> calls x
      x -> concatMap calls (children x)
    owners = [(ruleName r, locsOf r) | r <- templates]
    note d@(Diagnostic l msg) = case mapMaybe (\(n, ls) -> if S.member l ls then Just n else Nothing) owners of
      n : _ | Just c <- M.lookup n firstCall -> Diagnostic l (msg <> " (in the template " <> n <> ", expanded at " <> showLoc c <> ")")
      _ -> d
    showLoc (Loc a b) = T.pack (show a) <> ":" <> T.pack (show b)

-- A small state monad, so that peg-grammar keeps its dependencies.
data St = St
  { stInstances :: M.Map (Text, String) Text
  , stPending :: [(Text, Rule, [Expr], [Maybe Text], Int, Loc)]
  , stErrors :: [Diagnostic]
  , stCount :: Int
  , stInstanceTypes :: M.Map Text Text
  , stInstanceNames :: S.Set Text
  }

newtype Expand a = Expand {runExpandFn :: St -> (a, St)}

instance Functor Expand where
  fmap f (Expand g) = Expand $ \s -> let (a, s') = g s in (f a, s')

instance Applicative Expand where
  pure a = Expand $ \s -> (a, s)
  Expand f <*> Expand g = Expand $ \s -> let (h, s') = f s; (a, s'') = g s' in (h a, s'')

instance Monad Expand where
  Expand g >>= k = Expand $ \s -> let (a, s') = g s in runExpandFn (k a) s'

runExpand :: Expand a -> St -> (a, St)
runExpand = runExpandFn

gets' :: (St -> a) -> Expand a
gets' f = Expand $ \s -> (f s, s)

modify' :: (St -> St) -> Expand ()
modify' f = Expand $ \s -> ((), f s)

addError :: Diagnostic -> Expand ()
addError d = modify' $ \st -> st {stErrors = d : stErrors st}
