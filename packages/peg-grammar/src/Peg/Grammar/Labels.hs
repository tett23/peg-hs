{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The static check of label safety (ADR 0028), and removing labels.
--
-- A label @e ^l@ is safe if, whenever @e@ fails, the whole parse would
-- fail in the grammar without any label. Other labels are thus treated as
-- absent: if every label is safe in this sense, an input is never thrown on
-- before the label-free grammar would reject it, and the two grammars
-- accept the same language. The check follows the failure of @e@ outwards
-- and, at every point where the parser would otherwise try another way
-- (a later alternative, the end of a repetition, a caller, the end of the
-- growth of left recursion), shows from the next character of the input
-- that the other way cannot succeed. A later alternative is compared after
-- the part it shares with what has matched, through calls of rules with the
-- same arguments, and against the texts that matched literals are known to
-- be; constant predicates are known to succeed or fail (ADR 0038). It is an
-- approximation: a label it calls safe is safe, but it may warn about a
-- safe label. Labels the author has checked can be listed in @%safe@, and
-- are then not reported. Each label is judged in the grammar without the
-- other labels (ADR 0029).
--
-- 'labelWarnings' takes the grammar after template expansion and
-- 'Peg.Grammar.Check.check'; @peg-hs gen@ reports its warnings, and fails
-- on them with @--Werror@:
--
-- @
-- case expandTemplates g0 >>= \\g -> g \<$ check g of
--   Left diags -> ...
--   Right g -> mapM_ (TIO.putStrLn . renderDiagnostic file) (templateNotes g0 (labelWarnings g))
-- @
--
-- 'stripLabels' and 'stripLabelsAs' make the grammar without labels, to
-- test that the labelled grammar accepts the same inputs (ADR 0029).
module Peg.Grammar.Labels
  ( labelWarnings
  , labelSafeAt
  , matchesEmpty
  , stripLabels
  , stripLabelsAs
  ) where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.Char (isAlpha, isAlphaNum)
import Data.List (sortOn)
import Data.Maybe (catMaybes)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar

-- Character sets -------------------------------------------------------------

-- A set of characters, as sorted disjoint ranges of code points, and
-- whether it contains the end of the input.
data CharSet = CharSet [(Int, Int)] Bool
  deriving (Eq, Ord, Show)

maxCode :: Int
maxCode = 0x10FFFF

none, everything, anyChar, endOfInput :: CharSet
none = CharSet [] False
everything = CharSet [(0, maxCode)] True
anyChar = CharSet [(0, maxCode)] False
endOfInput = CharSet [] True

ranges :: [(Char, Char)] -> CharSet
ranges rs = CharSet (normalise [(fromEnum a, fromEnum b) | (a, b) <- rs, a <= b]) False

single :: Char -> CharSet
single c = ranges [(c, c)]

normalise :: [(Int, Int)] -> [(Int, Int)]
normalise = merge . sortOn fst
  where
    merge ((a, b) : (c, d) : rest)
      | c <= b + 1 = merge ((a, max b d) : rest)
      | otherwise = (a, b) : merge ((c, d) : rest)
    merge rs = rs

union :: CharSet -> CharSet -> CharSet
union (CharSet a e) (CharSet b f) = CharSet (normalise (a ++ b)) (e || f)

intersect :: CharSet -> CharSet -> CharSet
intersect (CharSet a e) (CharSet b f) = CharSet (go a b) (e && f)
  where
    go ((x1, y1) : xs) ((x2, y2) : ys)
      | y1 < x2 = go xs ((x2, y2) : ys)
      | y2 < x1 = go ((x1, y1) : xs) ys
      | otherwise =
          (max x1 x2, min y1 y2) : if y1 < y2 then go xs ((x2, y2) : ys) else go ((x1, y1) : xs) ys
    go _ _ = []

minus :: CharSet -> CharSet -> CharSet
minus (CharSet a e) (CharSet b f) = CharSet (go a b) (e && not f)
  where
    go [] _ = []
    go xs [] = xs
    go ((x1, y1) : xs) ((x2, y2) : ys)
      | y2 < x1 = go ((x1, y1) : xs) ys
      | y1 < x2 = (x1, y1) : go xs ((x2, y2) : ys)
      | otherwise =
          [(x1, x2 - 1) | x1 < x2] ++ (if y2 < y1 then go ((y2 + 1, y1) : xs) ys else go xs ((x2, y2) : ys))

isEmpty :: CharSet -> Bool
isEmpty (CharSet rs e) = null rs && not e

meets :: CharSet -> CharSet -> Bool
meets a b = not (isEmpty (intersect a b))

-- The abstraction of an expression --------------------------------------------

-- What the next character of the input can be for an expression: when it
-- succeeds consuming input (the first consumed character), when it
-- succeeds without consuming (the next character), and the characters on
-- which it surely does not fail (an under-approximation; a throw is not a
-- failure).
data Abs = Abs
  { absConsume :: CharSet
  , absEmpty :: CharSet
  , absSure :: CharSet
  }
  deriving (Eq, Show)

bottom :: Abs
bottom = Abs none none none

epsilon :: Abs
epsilon = Abs none everything everything

possible :: Abs -> CharSet
possible a = absConsume a `union` absEmpty a

andThen :: Abs -> Abs -> Abs
andThen x y =
  Abs
    { absConsume = absConsume x `union` (absEmpty x `intersect` absConsume y)
    , absEmpty = absEmpty x `intersect` absEmpty y
    , absSure = if absSure y == everything then absSure x else none
    }

orElse :: Abs -> Abs -> Abs
orElse x y = Abs (absConsume x `union` absConsume y) (absEmpty x `union` absEmpty y) (absSure x `union` absSure y)

-- The abstraction of the rules is a fixed point. The sure sets of negative
-- lookaheads depend on the possible sets and the other way round, so they
-- are computed in turn: possible sets with no sure sets, sure sets from
-- those, and possible sets again from the sure sets.
type Env = M.Map Text Abs

data Pass = Pass {passEnv :: Env, passNotEmpty :: Expr -> CharSet, passNotSure :: Expr -> CharSet}

ruleAbs :: Pass -> Rule -> Abs
ruleAbs p r = foldr orElse bottom [seqAbs p (altItems a) | a <- ruleAlts r]

seqAbs :: Pass -> [Item] -> Abs
seqAbs p = foldr (\i acc -> exprAbs p (itemExpr i) `andThen` acc) epsilon

exprAbs :: Pass -> Expr -> Abs
exprAbs p = \case
  ELit t _ -> case T.uncons t of
    Nothing -> epsilon
    Just (c, rest) -> Abs (single c) none (if T.null rest then single c else none)
  EClass rs _ -> let s = ranges rs in Abs s none s
  EAny -> Abs anyChar none anyChar
  ERef _ n _ -> M.findWithDefault bottom n (passEnv p)
  EGroup alts -> foldr orElse bottom (map (seqAbs p) alts)
  EStar x -> Abs (absConsume (exprAbs p x)) everything everything
  EPlus x -> let a = exprAbs p x in Abs (absConsume a) (absEmpty a) (absSure a)
  EOpt x -> Abs (absConsume (exprAbs p x)) everything everything
  EAnd x -> let a = exprAbs p x in Abs none (possible a) (absSure a)
  ENot x -> Abs none (passNotEmpty p x) (passNotSure p x)
  ECapture x -> exprAbs p x
  ELabel _ x _ -> exprAbs p x
  EDiscard x -> exprAbs p x
  ETemplate {} -> Abs everything everything none
  EPred b c -> case constantPred b c of
    Just True -> epsilon
    Just False -> bottom
    Nothing -> Abs none everything none

-- | The value of a predicate whose code is the constant @True@ or @False@
-- (ADR 0038): @&{ False }@ and @!{ True }@ never succeed, @&{ True }@ and
-- @!{ False }@ always do.
constantPred :: Bool -> Located Text -> Maybe Bool
constantPred positive (Located _ c) = case T.strip c of
  "True" -> Just positive
  "False" -> Just (not positive)
  _ -> Nothing

fixpoint :: [Rule] -> (Env -> Pass) -> Env
fixpoint rules mk = go (M.fromList [(ruleName r, bottom) | r <- rules]) (0 :: Int)
  where
    go env n
      | env' == env || n > 1000 = env
      | otherwise = go env' (n + 1)
      where
        env' = M.fromList [(ruleName r, ruleAbs (mk env) r) | r <- rules]

abstractions :: [Rule] -> (Env, Pass)
abstractions rules = (env3, final)
  where
    pass1 env = Pass env (const everything) (const none)
    env1 = fixpoint rules pass1
    possible1 x = possible (exprAbs (pass1 env1) x)
    pass2 env = Pass env (const everything) (\x -> everything `minus` possible1 x)
    env2 = fixpoint rules pass2
    sure2 x = absSure (exprAbs (pass2 env2) x)
    pass3 env = Pass env (\x -> everything `minus` sure2 x) (\x -> everything `minus` possible1 x)
    env3 = fixpoint rules pass3
    final = pass3 env3

-- Contexts ---------------------------------------------------------------------

-- Where an expression is, from the innermost frame outwards.
data Frame
  = -- | The items of a sequence and the index of the current one.
    FSeq [Item] Int
  | -- | The alternatives of a choice, with their locations, the index of the
    -- current one, and whether they are the body of a rule.
    FAlts [(Loc, [Item])] Int Bool
  | FStar Expr Loc
  | FPlus Expr Loc
  | FOpt
  | -- | A lookahead, with the location of its item.
    FAnd Loc
  | FNot Loc
  | FLabel
  | FCapture

frameKey :: Frame -> (Int, Int)
frameKey = \case
  FSeq _ j -> (0, j)
  FAlts _ i _ -> (1, i)
  FStar _ _ -> (2, 0)
  FPlus _ _ -> (3, 0)
  FOpt -> (4, 0)
  FAnd _ -> (5, 0)
  FNot _ -> (6, 0)
  FLabel -> (7, 0)
  FCapture -> (8, 0)

-- A label or a rule reference, in its rule and context.
data Site = Site Text [Frame] Loc Expr

siteRule :: Site -> Text
siteRule (Site r _ _ _) = r

siteFrames :: Site -> [Frame]
siteFrames (Site _ fs _ _) = fs

sites :: Rule -> [Site]
sites r =
  concat
    [ itemSites (FSeq items j : FAlts alts i True : []) item
    | (i, (_, items)) <- zip [0 ..] alts
    , (j, item) <- zip [0 ..] items
    ]
  where
    alts = [(altLoc a, altItems a) | a <- ruleAlts r]
    itemSites fs i = exprSites fs (itemLoc i) (itemExpr i)
    exprSites fs l e =
      [Site (ruleName r) fs l e | isSite e]
        ++ case e of
          EGroup gs ->
            let galts = [(maybe l itemLoc (headMay is), is) | is <- gs]
             in concat
                  [ itemSites (FSeq is j : FAlts galts k False : fs) item
                  | (k, (_, is)) <- zip [0 ..] galts
                  , (j, item) <- zip [0 ..] is
                  ]
          EStar x -> exprSites (FStar x l : fs) l x
          EPlus x -> exprSites (FPlus x l : fs) l x
          EOpt x -> exprSites (FOpt : fs) l x
          EAnd x -> exprSites (FAnd l : fs) l x
          ENot x -> exprSites (FNot l : fs) l x
          ECapture x -> exprSites (FCapture : fs) l x
          ELabel _ x _ -> exprSites (FLabel : fs) l x
          EDiscard x -> exprSites (FCapture : fs) l x
          _ -> []
    isSite = \case
      ELabel {} -> True
      ERef {} -> True
      _ -> False
    headMay = \case
      x : _ -> Just x
      [] -> Nothing

-- The check --------------------------------------------------------------------

data Verdict
  = Safe
  | -- | Where the other way is, and what it is.
    Unsafe Text
  | Unchecked Text
  deriving (Eq)

andAlso :: Verdict -> Verdict -> Verdict
andAlso Safe v = v
andAlso v _ = v

data Mode = Failed | Succeeded
  deriving (Eq, Ord)

data Ctx = Ctx
  { ctxPass :: Pass
  , ctxCallers :: M.Map Text [Site]
  , ctxEntries :: Set Text
  , ctxRecovery :: Set Text
  , ctxDirectLr :: Set Text
  -- ^ Rules with direct left recursion only, whose growing alternatives
  -- start with a call of the rule itself.
  , ctxOtherLr :: Set Text
  -- ^ Other rules taking part in left recursion.
  , ctxGrowing :: Text -> Int -> Bool
  -- ^ Whether an alternative of a rule is a growing one.
  , ctxRules :: M.Map Text Rule
  , ctxExpandable :: Set Text
  -- ^ Rules whose calls can be replaced by their alternatives (ADR 0038).
  }

-- The rule, the frames, the mode, the next characters, and the items known
-- to have matched (ADR 0038).
type Visited = Set (Text, [(Int, Int)], Mode, CharSet, Text)

-- The contexts already followed, so that recursion in the grammar ends.
newtype State s a = State {runState :: s -> (a, s)}

instance Functor (State s) where
  fmap f (State g) = State $ \s -> let (a, s') = g s in (f a, s')

instance Applicative (State s) where
  pure a = State $ \s -> (a, s)
  State f <*> State g = State $ \s -> let (h, s') = f s; (a, s'') = g s' in (h a, s'')

instance Monad (State s) where
  State g >>= k = State $ \s -> let (a, s') = g s in runState (k a) s'

evalState :: State s a -> s -> a
evalState m s = fst (runState m s)

gets :: (s -> a) -> State s a
gets f = State $ \s -> (f s, s)

modify' :: (s -> s) -> State s ()
modify' f = State $ \s -> let s' = f s in s' `seq` ((), s')

-- | Warnings for labels that may make the grammar reject valid input, or
-- that cannot be checked, except labels listed in @%safe@. The grammar
-- must have its templates expanded and must have passed
-- 'Peg.Grammar.Check.check'. Each warning is located at the label and its
-- message begins with @the label NAME may reject valid input@ or
-- @the label NAME cannot be checked@.
labelWarnings :: Grammar -> [Diagnostic]
labelWarnings g =
  [ Diagnostic l msg
  | Site rule fs l (ELabel _ x name) <- concatMap sites (grammarRules g)
  , name `notElem` safe
  , Just msg <- [verdictMessage name (verdictOf ctx rule fs x)]
  ]
  where
    safe = map unLoc (grammarSafe g)
    ctx = context g

-- | Whether a label put on an item of a rule would be safe: the check of
-- 'labelWarnings', for a label that is not in the grammar (ADR 0054). The
-- grammar must have its templates expanded and must have passed
-- 'Peg.Grammar.Check.check'.
--
-- The item is given by the name of its rule and a path of
-- @(alternative, item)@ indices from 0: the first pair picks an item of the
-- rule's body, and each following pair an item of the group that the
-- previous item contains through repetitions, options, captures and labels.
-- The label goes on the item's expression, inside the captures @$@ that
-- wrap it, as in @$(e ^l)@. A path that does not lead to an item is not
-- safe.
--
-- Apply it to the grammar once and to many items: the analysis of the
-- grammar is shared.
--
-- @
-- let safe = labelSafeAt g
-- in filter (uncurry safe) [("List", [(0, 2)]), ("List", [(0, 3), (0, 1)])]
-- @
labelSafeAt :: Grammar -> Text -> [(Int, Int)] -> Bool
labelSafeAt g = safeAt
  where
    ctx = context g
    safeAt rule path = case M.lookup rule (ctxRules ctx) >>= \r -> framesAt r path of
      Just (fs, x) -> verdictOf ctx rule fs x == Safe
      Nothing -> False

-- The frames of the item at a path, as 'sites' makes them, and its
-- expression without the captures around it.
framesAt :: Rule -> [(Int, Int)] -> Maybe ([Frame], Expr)
framesAt r = \case
  [] -> Nothing
  (i, j) : rest -> do
    let alts = [(altLoc a, altItems a) | a <- ruleAlts r]
    items <- index i (map snd alts)
    item <- index j items
    go (itemLoc item) [FSeq items j, FAlts alts i True] (itemExpr item) rest
  where
    go l fs e = \case
      [] -> Just (uncapture fs e)
      p@((k, m) : rest) -> case e of
        EGroup gs -> do
          let galts = [(maybe l itemLoc (headMay is), is) | is <- gs]
          is <- index k gs
          item <- index m is
          go (itemLoc item) (FSeq is m : FAlts galts k False : fs) (itemExpr item) rest
        EStar x -> go l (FStar x l : fs) x p
        EPlus x -> go l (FPlus x l : fs) x p
        EOpt x -> go l (FOpt : fs) x p
        ECapture x -> go l (FCapture : fs) x p
        ELabel _ x _ -> go l (FLabel : fs) x p
        EDiscard x -> go l (FCapture : fs) x p
        _ -> Nothing
    uncapture fs = \case
      ECapture x -> uncapture (FCapture : fs) x
      x -> (fs, x)
    index n xs = case drop n xs of
      x : _ | n >= 0 -> Just x
      _ -> Nothing
    headMay = \case
      x : _ -> Just x
      [] -> Nothing

-- The verdict on a label on the expression x, at the frames of a rule.
verdictOf :: Ctx -> Text -> [Frame] -> Expr -> Verdict
verdictOf ctx rule fs x = evalState (failed ctx rule fs ([], 0) (everything `minus` absSure (exprAbs (ctxPass ctx) x))) S.empty

-- | Whether an expression can match the empty string, in a grammar whose
-- templates are expanded: the judgement the label check uses. A predicate,
-- a lookahead, a repetition with @*@ and an option match the empty string;
-- a reference does when its rule can.
matchesEmpty :: Grammar -> Expr -> Bool
matchesEmpty g = nullableExpr (nullableRules (grammarRules g))

-- The analysis of a grammar for the check, made once.
context :: Grammar -> Ctx
context g =
  Ctx
    { ctxPass = pass
    , ctxCallers = callers
    , ctxEntries = S.fromList (start : map unLoc (grammarEntries g))
    , ctxRecovery = S.fromList [unLoc r | (_, r) <- grammarRecovers g]
    , ctxDirectLr = direct
    , ctxOtherLr = other
    , ctxGrowing = growing
    , ctxRules = M.fromList [(ruleName r, r) | r <- rules]
    , ctxExpandable = S.fromList [ruleName r | r <- rules, expandable r] `S.difference` (direct `S.union` other)
    }
  where
    rules = grammarRules g
    (_, pass) = abstractions rules
    callers = M.fromListWith (flip (++)) [(n, [s]) | r <- rules, s@(Site _ _ _ (ERef _ n _)) <- sites r]
    start = case (grammarStart g, rules) of
      (Just s, _) -> unLoc s
      (Nothing, r : _) -> ruleName r
      _ -> ""
    (direct, other, growing) = leftRecursion rules
    expandable r = not (any (any (exprMentions isTemplateOrEnv . itemExpr) . altItems) (ruleAlts r))
    isTemplateOrEnv = \case
      ETemplate {} -> True
      e -> any (elem "_env" . identifiers) (exprCodes e)

verdictMessage :: Text -> Verdict -> Maybe Text
verdictMessage name = \case
  Safe -> Nothing
  Unsafe why -> Just ("the label " <> name <> " may reject valid input: where it fails, " <> why)
  Unchecked why -> Just ("the label " <> name <> " cannot be checked: " <> why)

showLoc :: Loc -> Text
showLoc (Loc l c) = T.pack (show l) <> ":" <> T.pack (show c)

visit :: Text -> [Frame] -> Mode -> ([Item], Int) -> CharSet -> State Visited Verdict -> State Visited Verdict
visit rule fs mode (pre, lifts) k act = do
  let key = (rule, map frameKey fs, mode, k, T.pack (show (lifts, map (plainExpr . itemExpr) pre)))
  seen <- gets (S.member key)
  if seen then pure Safe else modify' (S.insert key) >> act

allOf :: [State Visited Verdict] -> State Visited Verdict
allOf = foldr (\a acc -> a >>= \v -> if v == Safe then acc else pure v) (pure Safe)

-- The expression of the innermost frame failed after the items pre had
-- matched from its start, and the next character is then in k. The items
-- let a later alternative that starts the same way, even through calls of
-- rules, be compared after the common part (ADR 0038).
failed :: Ctx -> Text -> [Frame] -> ([Item], Int) -> CharSet -> State Visited Verdict
failed ctx rule fs (pre0, lifts) k0 = visit rule fs Failed (pre, lifts) k $ case fs of
  FSeq items j : FAlts alts i body : rest -> do
    let matched = take j items ++ pre
        kAt m = beforeItems ctx (drop m matched) k
        growingAlt = body && S.member rule (ctxDirectLr ctx) && ctxGrowing ctx rule i
        later =
          [ (al, a)
          | (i', (al, a)) <- drop (i + 1) (zip [0 ..] alts)
          , not growingAlt || ctxGrowing ctx rule i'
          ]
        laterCheck (al, a)
          | commonPrefix items a > j = Safe
          | otherwise = foldr andAlso Safe [compareWith al a' | a' <- expansions ctx expandDepth matched a]
        compareWith al a' =
          let m = commonPrefix matched a'
              rest' = drop m a'
           in if possible (seqAbs (ctxPass ctx) rest') `meets` kAt m && not (knownFails ctx (drop m matched) rest')
                then Unsafe ("the alternative at " <> showLoc al <> " can match")
                else Safe
    if body && S.member rule (ctxOtherLr ctx) && ctxGrowing ctx rule i
      then pure (Unchecked ("it is in a growing alternative of " <> rule <> ", which takes part in indirect or hidden left recursion"))
      else case foldr andAlso Safe (map laterCheck later) of
        Safe
          | growingAlt -> succeeded ctx rule [] (kAt 1)
          | otherwise -> failed ctx rule rest (matched, lifts) k
        v -> pure v
  FStar _ _ : rest -> succeeded ctx rule rest kStart
  FPlus _ _ : rest -> allOf [failed ctx rule rest (pre, lifts) k, succeeded ctx rule rest kStart]
  FOpt : rest -> succeeded ctx rule rest kStart
  -- A throw inside a lookahead is a failure of the lookahead's body, which
  -- has failed here without the label too.
  FAnd _ : _ -> pure Safe
  FNot _ : _ -> pure Safe
  FLabel : rest -> failed ctx rule rest (pre, lifts) k
  FCapture : rest -> failed ctx rule rest (pre, lifts) k
  [] -> ruleFailed ctx rule (pre, lifts) k
  _ -> pure Safe
  where
    -- A long prefix is replaced by the characters at its start, so that
    -- following recursion in the grammar ends.
    (pre, k) = if length pre0 > maxPrefix then ([], beforeItems ctx pre0 k0) else (pre0, k0)
    kStart = beforeItems ctx pre k

-- The next character at the start of a sequence that matched and was
-- followed by a character in k.
beforeItems :: Ctx -> [Item] -> CharSet -> CharSet
beforeItems ctx prefix k = let a = seqAbs (ctxPass ctx) prefix in absConsume a `union` (absEmpty a `intersect` k)

-- Bounds that make the following of calls end: the matched items, the
-- code after replacing parameters (a recursive call wraps the arguments in
-- parentheses again at each level), the calls the items are carried
-- through, and the depth of expanding calls.
maxPrefix, maxCode', maxLifts, expandDepth :: Int
maxPrefix = 8
maxLifts = 3
maxCode' = 64
expandDepth = 8

-- The next character is in k at the end of an expression that succeeded.
succeeded :: Ctx -> Text -> [Frame] -> CharSet -> State Visited Verdict
succeeded ctx rule fs k = visit rule fs Succeeded ([], 0) k $ case fs of
  FSeq items j : alts@(FAlts _ i body) : rest -> do
    let after = drop (j + 1) items
        a = seqAbs (ctxPass ctx) after
        growingAlt = body && S.member rule (ctxDirectLr ctx) && ctxGrowing ctx rule i
        ended k'
          | growingAlt = allOf (succeeded ctx rule [] k' : [succeeded ctx rule [FSeq is 0, FAlts as' gi True] k' | FAlts as' _ _ <- [alts], (gi, (_, is)) <- zip [0 ..] as', ctxGrowing ctx rule gi])
          | otherwise = succeeded ctx rule rest k'
    if body && S.member rule (ctxOtherLr ctx) && ctxGrowing ctx rule i
      then pure (Unchecked ("it reaches a growing alternative of " <> rule <> ", which takes part in indirect or hidden left recursion"))
      else
        case after of
          next : _ | absConsume a `meets` k -> pure (Unsafe ("the parse can continue at " <> showLoc (itemLoc next)))
          _ ->
            allOf $
              [failed ctx rule (FSeq items (j + 1) : alts : rest) ([], 0) k | not (null after)]
                ++ [failed ctx rule (FSeq items m : alts : rest) ([], 0) everything | m <- [j + 2 .. length items - 1]]
                ++ [ended (absEmpty a `intersect` k) | absEmpty a `meets` k]
  FStar x l : rest -> again x l rest
  FPlus x l : rest -> again x l rest
  FOpt : rest -> succeeded ctx rule rest k
  -- Without the label, the body of the lookahead can succeed, while the
  -- throw makes it fail: the lookahead decides the other way.
  FAnd l : _ -> pure (Unsafe ("the lookahead at " <> showLoc l <> " can match"))
  FNot l : _ -> pure (Unsafe ("the lookahead at " <> showLoc l <> " can match"))
  FLabel : rest -> succeeded ctx rule rest k
  FCapture : rest -> succeeded ctx rule rest k
  [] -> ruleSucceeded ctx rule k
  _ -> pure Safe
  where
    again x l rest
      | possible (exprAbs (ctxPass ctx) x) `meets` k = pure (Unsafe ("the repetition at " <> showLoc l <> " can continue"))
      | otherwise = succeeded ctx rule rest k

ruleFailed :: Ctx -> Text -> ([Item], Int) -> CharSet -> State Visited Verdict
ruleFailed ctx rule (pre, lifts) k
  | S.member rule (ctxRecovery ctx) = pure Safe
  | otherwise = allOf [uncurry (failed ctx (siteRule s) (siteFrames s)) (lift s) | s <- callersOf ctx rule]
  where
    -- The matched items in the caller: the parameters are replaced by the
    -- arguments of the call. Without that, only their first characters.
    lift (Site _ _ _ (ERef _ _ args))
      | lifts < maxLifts
      , Just pre' <- M.lookup rule (ctxRules ctx) >>= \r -> paramMap r args >>= \pm -> substItems pm pre
      , all ((<= maxCode') . T.length) (concatMap (exprCodes . itemExpr) pre') =
          ((pre', lifts + 1), k)
    lift _ = (([], 0), beforeItems ctx pre k)

ruleSucceeded :: Ctx -> Text -> CharSet -> State Visited Verdict
ruleSucceeded ctx rule k
  | S.member rule (ctxRecovery ctx) = pure Safe
  | S.member rule (ctxEntries ctx) && k `meets` endOfInput = pure (Unsafe ("the input can end after the rule " <> rule <> ", which is an entry"))
  | otherwise = allOf [succeeded ctx (siteRule s) (siteFrames s) k | s <- callersOf ctx rule]

-- The calls of a rule, except the calls that start the growing alternatives
-- of the rule itself: those read the seed, not the result of a call.
callersOf :: Ctx -> Text -> [Site]
callersOf ctx rule =
  [ s
  | s <- M.findWithDefault [] rule (ctxCallers ctx)
  , not (isSeed s)
  ]
  where
    isSeed s = case siteFrames s of
      [FSeq _ 0, FAlts _ i True] -> siteRule s == rule && S.member rule (ctxDirectLr ctx) && ctxGrowing ctx rule i
      _ -> False

-- The length of the common prefix of two sequences, ignoring locations
-- and bindings. Two items whose code reads a binding are the same only if
-- the bindings before them are (ADR 0038).
commonPrefix :: [Item] -> [Item] -> Int
commonPrefix = go 0 [] []
  where
    go n bx by (a : as) (b : bs)
      | plainExpr (itemExpr a) == plainExpr (itemExpr b)
          && (bx == by || not (any (readsAny (catMaybes (bx ++ by))) (exprCodes (itemExpr a)))) =
          go (n + 1) (itemBind a : bx) (itemBind b : by) as bs
    go n _ _ _ _ = n
    readsAny names code = any (`elem` names) (identifiers code)

plainExpr :: Expr -> Expr
plainExpr = \case
  ERef _ n args -> ERef noLoc n [Located noLoc (unLoc a) | a <- args]
  EGroup alts -> EGroup (map (map (\i -> Item noLoc Nothing (plainExpr (itemExpr i)))) alts)
  EStar x -> EStar (plainExpr x)
  EPlus x -> EPlus (plainExpr x)
  EOpt x -> EOpt (plainExpr x)
  EAnd x -> EAnd (plainExpr x)
  ENot x -> ENot (plainExpr x)
  ECapture x -> ECapture (plainExpr x)
  -- The other labels are absent in the grammar the check is about.
  ELabel _ x _ -> plainExpr x
  EDiscard x -> EDiscard (plainExpr x)
  EPred b (Located _ c) -> EPred b (Located noLoc c)
  ETemplate _ n as vs -> ETemplate noLoc n (map plainExpr as) [Located noLoc (unLoc v) | v <- vs]
  e -> e
  where
    noLoc = Loc 0 0

-- The Haskell code of an expression: arguments and predicates.
exprCodes :: Expr -> [Text]
exprCodes = \case
  ERef _ _ args -> map unLoc args
  EPred _ c -> [unLoc c]
  e -> concatMap exprCodes (subExprs e)

exprMentions :: (Expr -> Bool) -> Expr -> Bool
exprMentions p e = p e || any (exprMentions p) (subExprs e)

subExprs :: Expr -> [Expr]
subExprs = \case
  EGroup alts -> map itemExpr (concat alts)
  EStar x -> [x]
  EPlus x -> [x]
  EOpt x -> [x]
  EAnd x -> [x]
  ENot x -> [x]
  ECapture x -> [x]
  ELabel _ x _ -> [x]
  EDiscard x -> [x]
  ETemplate _ _ as _ -> as
  _ -> []

-- The identifiers of Haskell code.
identifiers :: Text -> [Text]
identifiers = filter (\t -> maybe False (identStart . fst) (T.uncons t)) . T.split (not . identChar)
  where
    identStart c = isAlpha c || c == '_'

identChar :: Char -> Bool
identChar c = isAlphaNum c || c == '_' || c == '\''

-- Calls across rules (ADR 0038) -------------------------------------------------

-- The parameters of a rule and the arguments of a call, in parentheses.
paramMap :: Rule -> [Located Text] -> Maybe (M.Map Text Text)
paramMap r args
  | length (ruleParams r) == length args = Just (M.fromList (zip (map paramName (ruleParams r)) [paren (unLoc a) | a <- args]))
  | otherwise = Nothing
  where
    -- An identifier or a number stays as it is, so that the same argument
    -- passed on through several calls is written the same way.
    paren a
      | T.all identChar (T.strip a) && not (T.null (T.strip a)) = T.strip a
      | otherwise = "(" <> T.strip a <> ")"

-- Items with the parameters replaced, token by token, in their code.
-- Nothing when a binding has the name of a parameter, or when code that
-- reads a parameter may bind names itself.
substItems :: M.Map Text Text -> [Item] -> Maybe [Item]
substItems pm = mapM item
  where
    item (Item l b e)
      | maybe False (`M.member` pm) b = Nothing
      | otherwise = Item l b <$> expr e
    expr = \case
      ERef l n as -> ERef l n <$> mapM code as
      EPred b c -> EPred b <$> code c
      EGroup alts -> EGroup <$> mapM (mapM item) alts
      EStar x -> EStar <$> expr x
      EPlus x -> EPlus <$> expr x
      EOpt x -> EOpt <$> expr x
      EAnd x -> EAnd <$> expr x
      ENot x -> ENot <$> expr x
      ECapture x -> ECapture <$> expr x
      ELabel l x n -> (\x' -> ELabel l x' n) <$> expr x
      EDiscard x -> EDiscard <$> expr x
      ETemplate l n as vs -> ETemplate l n <$> mapM expr as <*> mapM code vs
      e -> Just e
    code (Located l c)
      | not (any (`M.member` pm) ws) = Just (Located l c)
      | any (`elem` ws) ["let", "where", "case", "of", "do"] || any (`T.isInfixOf` c) ["\\", "->", "<-"] = Nothing
      | otherwise = Just (Located l (rewrite c))
      where
        ws = identifiers c
    rewrite t = case T.uncons t of
      Nothing -> ""
      Just (c, _)
        | identChar c ->
            let (w, rest) = T.span identChar t
             in M.findWithDefault w w pm <> rewrite rest
        | otherwise -> let (o, rest) = T.break identChar t in o <> rewrite rest

-- The alternatives of a rule called with arguments, in the caller.
expandCall :: Ctx -> Text -> [Located Text] -> Maybe [[Item]]
expandCall ctx n args = do
  r <- M.lookup n (ctxRules ctx)
  if S.member n (ctxExpandable ctx) then Just () else Nothing
  pm <- paramMap r args
  mapM (substItems pm . altItems) (ruleAlts r)

-- A later alternative with the calls that differ from the matched items
-- replaced by the alternatives of their rules, each way it can go.
expansions :: Ctx -> Int -> [Item] -> [Item] -> [[Item]]
expansions ctx depth matched a =
  let m = commonPrefix matched a
   in case drop m a of
        Item l _ e : rest
          | m < length matched
          , depth > 0
          , Just alts <- unfold l e ->
              let xs = concat [expansions ctx (depth - 1) matched (take m a ++ alt ++ rest) | alt <- alts]
               in if length xs > maxExpansions then [a] else xs
        _ -> [a]
  where
    -- The ways an item can start: the alternatives of a call or a group,
    -- one iteration of a repetition, or nothing for an optional item.
    unfold l = \case
      ERef _ n args -> expandCall ctx n args
      EGroup alts -> Just alts
      EPlus x -> Just [[Item l Nothing x, Item l Nothing (EStar x)]]
      EStar x -> Just [[Item l Nothing x, Item l Nothing (EStar x)], []]
      EOpt x -> Just [[Item l Nothing x], []]
      ECapture x -> Just [[Item l Nothing x]]
      EDiscard x -> Just [[Item l Nothing x]]
      ELabel _ x _ -> Just [[Item l Nothing x]]
      _ -> Nothing

maxExpansions :: Int
maxExpansions = 64

-- Known prefixes (ADR 0038) ---------------------------------------------------

-- The texts that the input starts with, when matched items start with
-- literals: a literal, or a rule whose alternatives are literals.
knownStrings :: Ctx -> [Item] -> [Text]
knownStrings ctx items = filter (not . T.null) (go items)
  where
    go [] = [""]
    go (i : rest) = case literals (itemExpr i) of
      Just ts -> take 16 [T.take maxKnown (t <> s) | t <- ts, s <- if T.length t >= maxKnown then [""] else go rest]
      Nothing -> [""]
    literals = \case
      ELit t _ -> Just [t]
      ECapture x -> literals x
      ELabel _ x _ -> literals x
      EDiscard x -> literals x
      ERef _ n [] | Just r <- M.lookup n (ctxRules ctx), not (null (ruleAlts r)) -> concat <$> mapM (sequenceLiterals . altItems) (ruleAlts r)
      _ -> Nothing
    sequenceLiterals is = map T.concat . sequence <$> mapM (literalsOnly . itemExpr) is
    literalsOnly = \case
      ELit t _ -> Just [t]
      _ -> Nothing

maxKnown :: Int
maxKnown = 4

-- Whether a sequence fails on every input that starts with one of the known
-- texts.
knownFails :: Ctx -> [Item] -> [Item] -> Bool
knownFails ctx matched rest = case knownStrings ctx matched of
  [] -> False
  ss -> all (\t -> all (== SFail) (simSeq ctx expandDepth t (map itemExpr rest))) ss

-- The outcome of an expression on an input that starts with a known text:
-- it fails, it succeeds with the rest of the text left, or it cannot be
-- told from the text.
data Sim = SFail | SOk Text | SUnknown
  deriving (Eq)

simSeq :: Ctx -> Int -> Text -> [Expr] -> [Sim]
simSeq _ _ t [] = [SOk t]
simSeq ctx d t (e : es) = capSim (concatMap next (simExpr ctx d t e))
  where
    next = \case
      SOk t' -> simSeq ctx d t' es
      r -> [r]

capSim :: [Sim] -> [Sim]
capSim rs = let rs' = foldr (\r acc -> if r `elem` acc then acc else r : acc) [] rs in if length rs' > 16 then [SUnknown] else rs'

simExpr :: Ctx -> Int -> Text -> Expr -> [Sim]
simExpr ctx d t = \case
  ELit l _
    | T.null l -> [SOk t]
    | T.take n l /= T.take n t -> [SFail]
    | T.length l <= T.length t -> [SOk (T.drop (T.length l) t)]
    | otherwise -> [SUnknown]
    where
      n = min (T.length l) (T.length t)
  EClass rs _ -> one (\c -> any (\(a, b) -> a <= c && c <= b) rs)
  EAny -> one (const True)
  ERef _ n args
    | d > 0, Just alts <- expandCall ctx n args -> choice (d - 1) alts
    | otherwise -> [SUnknown]
  EGroup alts -> choice d alts
  EStar x -> star x t
  EPlus x -> capSim (concatMap (\case SOk t' -> star x t'; r -> [r]) (simExpr ctx d t x))
  EOpt x -> capSim (concatMap (\case SFail -> [SOk t]; r -> [r]) (simExpr ctx d t x))
  EAnd x -> let rs = simExpr ctx d t x in if all (== SFail) rs then [SFail] else if all isOk rs then [SOk t] else [SUnknown]
  ENot x -> let rs = simExpr ctx d t x in if all (== SFail) rs then [SOk t] else if all isOk rs then [SFail] else [SUnknown]
  ECapture x -> simExpr ctx d t x
  -- The other labels are absent in the grammar the check is about.
  ELabel _ x _ -> simExpr ctx d t x
  EDiscard x -> simExpr ctx d t x
  EPred b c -> case constantPred b c of
    Just True -> [SOk t]
    Just False -> [SFail]
    Nothing -> [SUnknown]
  ETemplate {} -> [SUnknown]
  where
    one p = case T.uncons t of
      Nothing -> [SUnknown]
      Just (c, rest) -> if p c then [SOk rest] else [SFail]
    isOk = \case
      SOk _ -> True
      _ -> False
    choice d' = \case
      [] -> [SFail]
      alt : rest ->
        let rs = simSeq ctx d' t (map itemExpr alt)
         in if all (== SFail) rs
              then choice d' rest
              else if SFail `notElem` rs then rs else capSim (filter (/= SFail) rs ++ choice d' rest)
    star x t' =
      capSim $
        concatMap
          ( \case
              SFail -> [SOk t']
              SOk t'' | T.length t'' < T.length t' -> star x t''
              SOk t'' -> [SOk t'']
              SUnknown -> [SUnknown]
          )
          (simExpr ctx d t' x)

-- Left recursion: rules with direct left recursion only, other rules in
-- left recursion, and which alternatives grow.
leftRecursion :: [Rule] -> (Set Text, Set Text, Text -> Int -> Bool)
leftRecursion rules = (direct, other, growing)
  where
    nullable = nullableRules rules
    altCalls a = leftCalls nullable (altItems a)
    edges r = S.toList (S.fromList (concatMap altCalls (ruleAlts r)))
    sccs = stronglyConnComp [(r, ruleName r, edges r) | r <- rules]
    component = M.fromList (concat [[(ruleName r, S.fromList (map ruleName rs)) | r <- rs] | CyclicSCC rs <- sccs] ++ [(ruleName r, S.singleton (ruleName r)) | AcyclicSCC r <- sccs, ruleName r `elem` edges r])
    ruleMap = M.fromList [(ruleName r, r) | r <- rules]
    growing n i = case (M.lookup n component, M.lookup n ruleMap) of
      (Just comp, Just r) | a : _ <- drop i (ruleAlts r) -> any (`S.member` comp) (altCalls a)
      _ -> False
    isDirect r = case M.lookup (ruleName r) component of
      Just comp ->
        comp == S.singleton (ruleName r)
          && and
            [ case altItems a of
                Item _ _ (ERef _ n []) : _ -> n == ruleName r
                _ -> False
            | (i, a) <- zip [0 ..] (ruleAlts r)
            , growing (ruleName r) i
            ]
      Nothing -> False
    inLr = M.keysSet component
    direct = S.fromList [ruleName r | r <- rules, S.member (ruleName r) inLr, isDirect r]
    other = inLr `S.difference` direct

nullableRules :: [Rule] -> Set Text
nullableRules rules = go S.empty
  where
    go known =
      let next = S.fromList [ruleName r | r <- rules, any (all (nullableExpr known . itemExpr) . altItems) (ruleAlts r)]
       in if next == known then known else go next

nullableExpr :: Set Text -> Expr -> Bool
nullableExpr known = \case
  ELit t _ -> T.null t
  EClass _ _ -> False
  EAny -> False
  ERef _ n _ -> S.member n known
  EGroup alts -> any (all (nullableExpr known . itemExpr)) alts
  EPlus x -> nullableExpr known x
  ECapture x -> nullableExpr known x
  ELabel _ x _ -> nullableExpr known x
  EDiscard x -> nullableExpr known x
  _ -> True

leftCalls :: Set Text -> [Item] -> [Text]
leftCalls known = go
  where
    go [] = []
    go (i : is) = calls (itemExpr i) ++ (if nullableExpr known (itemExpr i) then go is else [])
    calls = \case
      ERef _ n _ -> [n]
      EGroup alts -> concatMap go alts
      EStar x -> calls x
      EPlus x -> calls x
      EOpt x -> calls x
      EAnd x -> calls x
      ENot x -> calls x
      ECapture x -> calls x
      ELabel _ x _ -> calls x
      EDiscard x -> calls x
      _ -> []

-- Removing labels -----------------------------------------------------------------

-- | 'stripLabels', generating another module: the 'Text' is the name of
-- the module (@peg-hs gen --strip-labels MODULE@).
stripLabelsAs :: Text -> Grammar -> Grammar
stripLabelsAs m g = (stripLabels g) {grammarModule = Located (locOf (grammarModule g)) m}

-- | The grammar without its labels, @%recover@ and @%safe@ directives. It
-- accepts the language the labelled grammar accepts when every label is
-- safe. Rules used only for recovery become entries, so that the code they
-- use stays used.
stripLabels :: Grammar -> Grammar
stripLabels g =
  g
    { grammarRecovers = []
    , grammarSafe = []
    , grammarEntries = grammarEntries g ++ recoveryEntries
    , grammarRules = [r {ruleAlts = map alt (ruleAlts r)} | r <- grammarRules g]
    }
  where
    -- One entry for each recovery rule that is not an entry or the start
    -- rule already, however many labels it recovers (ADR 0038).
    recoveryEntries = go (start : map unLoc (grammarEntries g)) [r | (_, r) <- grammarRecovers g]
      where
        go _ [] = []
        go seen (r : rs)
          | unLoc r `elem` seen = go seen rs
          | otherwise = r : go (unLoc r : seen) rs
    start = case (grammarStart g, grammarRules g) of
      (Just s, _) -> unLoc s
      (Nothing, r : _) -> ruleName r
      _ -> ""
    alt a = a {altItems = map item (altItems a)}
    item i = i {itemExpr = expr (itemExpr i)}
    expr = \case
      ELabel _ x _ -> expr x
      EDiscard x -> EDiscard (expr x)
      EGroup alts -> EGroup (map (map item) alts)
      EStar x -> EStar (expr x)
      EPlus x -> EPlus (expr x)
      EOpt x -> EOpt (expr x)
      EAnd x -> EAnd (expr x)
      ENot x -> ENot (expr x)
      ECapture x -> ECapture (expr x)
      e -> e
