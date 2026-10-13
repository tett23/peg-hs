{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Expanding rule templates (ADR 0031).
--
-- A call of a template, @List<Exp, ','>@, becomes a reference to an
-- instance of the template: an ordinary rule made for each distinct list of
-- arguments, with the parameters replaced by the arguments. The grammar
-- that results has no template, and the static checks, left recursion and
-- code generation treat the instances as ordinary rules.
--
-- An argument may use the parameters of the rule that calls the template
-- (ADR 0055). The instance then takes those parameters, in the order of
-- their names and with the types of the caller's annotation, and the call
-- passes them on: @Lines<Item(ind)>@ in @B(ind :: Int)@ becomes
-- @Lines'0(ind)@. An argument cannot use a binding of the caller.
--
-- A template may also have value parameters, declared in its annotation
-- as @Indented<p>(n :: Int)@ and passed as @Indented<Item>(ind + 2)@. The
-- instance takes them before the parameters of the caller, and the values
-- are not part of what makes an instance: calls that differ only in their
-- values share one.
--
-- Expand before 'Peg.Grammar.Check.check' and
-- 'Peg.Grammar.Labels.labelWarnings', and pass their diagnostics through
-- 'templateNotes' so that an error inside a template names the call that
-- expanded it:
--
-- @
-- case expandTemplates g0 >>= check of
--   Left diags -> reportErrors (templateNotes g0 diags)
--   Right analysis -> ...
-- @
--
-- "Peg.Grammar" shows the whole sequence of checks.
module Peg.Grammar.Templates
  ( expandTemplates
  , templateNotes
  ) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isUpper)
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
--
-- A grammar with neither templates nor template calls is returned as it is.
-- A template call in a grammar without templates is still an error, such
-- as @rule B is not a template@ (ADR 0052).
expandTemplates :: Grammar -> Either [Diagnostic] Grammar
expandTemplates g
  | M.null templates && not (any callsTemplate (grammarRules g)) = Right g
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
        ++ [ Diagnostic (ruleLoc r) ("the template " <> ruleName r <> " has two parameters named " <> p)
           | r <- M.elems templates
           , let names = map templateParamName (ruleTemplateParams r)
           , p <- nub [x | x <- names, length (filter (== x) names) > 1]
           ]

    expandRule r = do
      let caller = Caller (ruleName r) (M.fromList [(paramName p, paramType p) | p <- ruleParams r])
      alts <- mapM (expandAlt caller 0 S.empty) (ruleAlts r)
      pure r {ruleAlts = alts}

    -- The bindings to the left of an item are in its scope; those in a
    -- group are not in scope after the group.
    expandAlt caller depth scope a = do
      items <- expandItems caller depth scope (altItems a)
      pure a {altItems = items}

    expandItems caller depth scope = \case
      [] -> pure []
      i : is -> do
        i' <- (\e -> i {itemExpr = e}) <$> expandExpr caller depth scope (itemExpr i)
        rest <- expandItems caller depth (maybe scope (`S.insert` scope) (itemBind i)) is
        pure (i' : rest)

    expandExpr caller depth scope = \case
      ERef l n args
        | M.member n templates -> do
            addError (Diagnostic l ("the template " <> n <> " needs arguments: " <> n <> "<...>"))
            pure (ERef l n args)
      ETemplate l n args vals -> case M.lookup n templates of
        Nothing -> do
          addError (Diagnostic l ("rule " <> n <> " is not a template"))
          pure (ERef l n [])
        Just t -> do
          -- The value arguments of the value parameters (ADR 0055).
          let valueParams = ruleParams t
          if null valueParams && not (null vals)
            then addError (Diagnostic l ("the template " <> n <> " takes no value arguments"))
            else
              if length vals /= length valueParams
                then addError (Diagnostic l ("the template " <> n <> " expects " <> T.pack (show (length valueParams)) <> " value argument(s), but got " <> T.pack (show (length vals))))
                else pure ()
          args' <- mapM (expandExpr caller depth scope) args
          let params = ruleTemplateParams t
          if length args' /= length params
            then do
              addError (Diagnostic l ("the template " <> n <> " expects " <> T.pack (show (length params)) <> " argument(s), but got " <> T.pack (show (length args'))))
              pure (ERef l n [])
            else do
              captured <- captures l caller scope t args'
              tys <- mapM (argType l) (zip params args')
              name <- instanceOf l depth t args' tys captured
              pure (ERef l name (vals ++ [Located l x | (x, _) <- captured]))
      EGroup alts -> EGroup <$> mapM (expandItems caller depth scope) alts
      EStar x -> EStar <$> expandExpr caller depth scope x
      EPlus x -> EPlus <$> expandExpr caller depth scope x
      EOpt x -> EOpt <$> expandExpr caller depth scope x
      EAnd x -> EAnd <$> expandExpr caller depth scope x
      ENot x -> ENot <$> expandExpr caller depth scope x
      ECapture x -> ECapture <$> expandExpr caller depth scope x
      ELabel l x n -> (\x' -> ELabel l x' n) <$> expandExpr caller depth scope x
      EDiscard x -> EDiscard <$> expandExpr caller depth scope x
      e -> pure e

    -- The parameters of the caller that the arguments of a call use, in
    -- the order of their names (ADR 0055). A binding of the caller cannot
    -- be taken, and a parameter cannot be taken under a name that the body
    -- of the template uses.
    captures l caller scope t args = do
      let names = S.fromList (concatMap (concatMap haskellIdents . exprCode) args)
          bound = [x | x <- S.toAscList names, S.member x scope]
          taken = [(x, ty) | x <- S.toAscList names, x `notElem` reservedBindings, not (S.member x scope), Just ty <- [M.lookup x (callerParams caller)]]
          inBody = M.findWithDefault S.empty (ruleName t) bodyNames
      mapM_ (\x -> addError (Diagnostic l ("the argument of the template " <> ruleName t <> " uses the binding " <> x <> ", which a template cannot take; pass it as a value argument"))) bound
      mapM_
        (\x -> addError (Diagnostic l ("the template " <> ruleName t <> " uses the name " <> x <> " in its body, so its argument cannot take the parameter " <> x <> " of the rule " <> callerName caller <> "; rename the parameter")))
        [x | (x, _) <- taken, S.member x inBody]
      pure taken

    -- The value parameters, the bindings and the identifiers of the code
    -- in the body of each template.
    bodyNames = M.map (\t -> S.fromList (map paramName (ruleParams t) ++ concatMap altNames (ruleAlts t))) templates
    altNames a = concatMap haskellIdents (altCode a) ++ concatMap itemBinds (altItems a)
    itemBinds i = maybe [] pure (itemBind i) ++ exprBinds (itemExpr i)
    exprBinds = \case
      EGroup alts -> concatMap (concatMap itemBinds) alts
      ETemplate _ _ args _ -> concatMap exprBinds args
      x -> concatMap exprBinds (exprChildren x)

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

    instanceOf l depth t args tys captured = do
      let key = (ruleName t, show (map plain args, [(x, unLoc ty) | (x, ty) <- captured]))
      existing <- gets' (M.lookup key . stInstances)
      case existing of
        Just name -> pure name
        Nothing -> do
          n <- gets' stCount
          let name = freshName (ruleName t) n
          modify' $ \st ->
            st
              { stInstances = M.insert key name (stInstances st)
              , stPending = stPending st ++ [(name, t, args, captured, depth + 1, l)]
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
        (name, t, args, captured, depth, l) : _ -> do
          modify' $ \st -> st {stPending = drop 1 (stPending st)}
          rule <-
            if depth > maxDepth || sum (map exprSize args) > maxSize
              then do
                addError (Diagnostic l ("the expansion of the template " <> ruleName t <> " does not end: templates call templates more than " <> T.pack (show maxDepth) <> " levels deep"))
                pure Nothing
              else do
                let sub = M.fromList (zip (map templateParamName (ruleTemplateParams t)) (zip (ruleTemplateParams t) args))
                    -- The calls in the body take the parameters of the
                    -- instance (ADR 0055).
                    caller = Caller (ruleName t) (M.fromList ([(paramName p, paramType p) | p <- ruleParams t] ++ captured))
                alts <- mapM (expandAlt caller depth S.empty . substituteAlt sub) (ruleAlts t)
                ty <- gets' (M.findWithDefault "()" name . stInstanceTypes)
                -- A parameter that the code of the instance does not use
                -- is named _x', so that the generated code has no warning.
                let used = S.fromList (concatMap (concatMap haskellIdents . altCode) alts)
                    params = ruleParams t ++ [Param (if S.member x used then x else "_" <> x <> "'") ty' | (x, ty') <- captured]
                pure (Just t {ruleName = name, ruleParams = params, ruleTemplateParams = [], ruleType = (ruleType t) {unLoc = ty}, ruleAlts = alts})
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
      -- A parameter passed on to a template is put as it is: the template
      -- called decides whether its value is used.
      ETemplate l n args vals -> ETemplate l n (map passed args) vals
      e -> e
    passed = \case
      ERef _ n [] | Just (_, arg) <- M.lookup n sub -> arg
      e -> expr e

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
  ETemplate _ _ args _ -> 1 + sum (map exprSize args)
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
  ETemplate _ n args vals -> ETemplate noLoc n (map plain args) [Located noLoc (unLoc v) | v <- vals]
  EDiscard x -> EDiscard (plain x)
  e -> e
  where
    noLoc = Loc 0 0

-- | Add to the diagnostics located in the body of a template the call that
-- expanded it, and remove duplicates: an error in a template is found once
-- for each instance. The grammar is the one before expansion. The note is
-- appended to the message as @(in the template NAME, expanded at L:C)@,
-- naming the first call of the template.
templateNotes :: Grammar -> [Diagnostic] -> [Diagnostic]
templateNotes g = nub . map note
  where
    templates = [r | r <- grammarRules g, not (null (ruleTemplateParams r))]
    firstCall = M.fromListWith (\_ old -> old) [(n, l) | r <- grammarRules g, a <- ruleAlts r, (l, n) <- concatMap (calls . itemExpr) (altItems a)]
    locsOf r = S.fromList (ruleLoc r : concat [altLoc a : concatMap itemLocs (altItems a) | a <- ruleAlts r])
    itemLocs i = itemLoc i : exprLocs (itemExpr i)
    exprLocs = \case
      ERef l _ args -> l : map locOf args
      ETemplate l _ args vals -> l : concatMap exprLocs args ++ map locOf vals
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
      ETemplate l n args _ -> (l, n) : concatMap calls args
      EGroup alts -> concatMap (concatMap (calls . itemExpr)) alts
      ELabel _ x _ -> calls x
      x -> concatMap calls (children x)
    owners = [(ruleName r, locsOf r) | r <- templates]
    note d@(Diagnostic l msg) = case mapMaybe (\(n, ls) -> if S.member l ls then Just n else Nothing) owners of
      n : _ | Just c <- M.lookup n firstCall -> Diagnostic l (msg <> " (in the template " <> n <> ", expanded at " <> showLoc c <> ")")
      _ -> d
    showLoc (Loc a b) = T.pack (show a) <> ":" <> T.pack (show b)

-- The rule whose body has a template call: its name, for the messages,
-- and its parameters (ADR 0055).
data Caller = Caller
  { callerName :: Text
  , callerParams :: M.Map Text (Located Text)
  }

-- The bindings that are not parameters of the caller, but are in the scope
-- of every action and argument.
reservedBindings :: [Text]
reservedBindings = ["_env", "_col", "_span"]

-- The Haskell code of an alternative: its action and the code in its
-- expressions.
altCode :: Alt -> [Text]
altCode a = maybe [] (pure . unLoc) (altAction a) ++ concatMap (exprCode . itemExpr) (altItems a)

-- The Haskell code in an expression: the arguments of rule calls and the
-- semantic predicates.
exprCode :: Expr -> [Text]
exprCode = \case
  ERef _ _ args -> map unLoc args
  EPred _ c -> [unLoc c]
  EGroup alts -> concatMap (concatMap (exprCode . itemExpr)) alts
  ETemplate _ _ args vals -> concatMap exprCode args ++ map unLoc vals
  x -> concatMap exprCode (exprChildren x)

exprChildren :: Expr -> [Expr]
exprChildren = \case
  EStar x -> [x]
  EPlus x -> [x]
  EOpt x -> [x]
  EAnd x -> [x]
  ENot x -> [x]
  ECapture x -> [x]
  ELabel _ x _ -> [x]
  EDiscard x -> [x]
  _ -> []

-- The variable names of a piece of Haskell code (ADR 0055). A qualified
-- name (M.x) is one name, and the text of string and character literals is
-- skipped. This is lexical: a name bound inside the code (\\x -> x) counts
-- too.
haskellIdents :: Text -> [Text]
haskellIdents t = case T.uncons t of
  Nothing -> []
  Just (c, rest)
    | c == '"' -> haskellIdents (skipString rest)
    | c == '\'' -> haskellIdents (skipChar rest)
    | isDigit c -> haskellIdents (T.dropWhile isIdent rest)
    | isAlpha c || c == '_' -> let (n, rest') = qualified t in n : haskellIdents rest'
    | otherwise -> haskellIdents rest
  where
    isIdent x = isAlphaNum x || x == '_' || x == '\''
    qualified s =
      let (n, rest) = T.span isIdent s
       in case T.uncons rest of
            Just ('.', after)
              | Just (h, _) <- T.uncons n
              , isUpper h
              , Just (a, _) <- T.uncons after
              , isAlpha a || a == '_' ->
                  let (m, rest') = qualified after in (n <> "." <> m, rest')
            _ -> (n, rest)
    skipString s = case T.uncons s of
      Nothing -> s
      Just ('\\', r) -> skipString (T.drop 1 r)
      Just ('"', r) -> r
      Just (_, r) -> skipString r
    -- A character literal; a quote that does not start one (a promoted
    -- constructor or a quoted name) is skipped alone.
    skipChar s = case T.unpack (T.take 2 s) of
      ['\\', _] -> T.drop 1 (T.dropWhile (/= '\'') (T.drop 2 s))
      [_, '\''] -> T.drop 2 s
      _ -> s

-- A small state monad, so that peg-grammar keeps its dependencies.
data St = St
  { stInstances :: M.Map (Text, String) Text
  , stPending :: [(Text, Rule, [Expr], [(Text, Located Text)], Int, Loc)]
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

-- Whether a rule calls a template anywhere in its alternatives.
callsTemplate :: Rule -> Bool
callsTemplate = any (any (expr . itemExpr) . altItems) . ruleAlts
  where
    expr = \case
      ETemplate {} -> True
      EGroup alts -> any (any (expr . itemExpr)) alts
      EStar x -> expr x
      EPlus x -> expr x
      EOpt x -> expr x
      EAnd x -> expr x
      ENot x -> expr x
      ECapture x -> expr x
      ELabel _ x _ -> expr x
      EDiscard x -> expr x
      _ -> False
