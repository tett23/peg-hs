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
-- that the other way cannot succeed. It is an approximation: a label it
-- calls safe is safe, but it may warn about a safe label.
module Peg.Grammar.Labels
  ( labelWarnings
  , stripLabels
  , stripLabelsAs
  ) where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (sortOn)
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
  EPred _ _ -> Abs none everything none

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
  | FAnd
  | FNot
  | FLabel
  | FCapture

frameKey :: Frame -> (Int, Int)
frameKey = \case
  FSeq _ j -> (0, j)
  FAlts _ i _ -> (1, i)
  FStar _ _ -> (2, 0)
  FPlus _ _ -> (3, 0)
  FOpt -> (4, 0)
  FAnd -> (5, 0)
  FNot -> (6, 0)
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
          EAnd x -> exprSites (FAnd : fs) l x
          ENot x -> exprSites (FNot : fs) l x
          ECapture x -> exprSites (FCapture : fs) l x
          ELabel _ x _ -> exprSites (FLabel : fs) l x
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
  }

type Visited = Set (Text, [(Int, Int)], Mode, CharSet)

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
-- that cannot be checked. The grammar must have passed
-- 'Peg.Grammar.Check.check'.
labelWarnings :: Grammar -> [Diagnostic]
labelWarnings g =
  [ Diagnostic l msg
  | Site rule fs l (ELabel _ x name) <- concatMap sites rules
  , name `notElem` safe
  , Just msg <- [verdictMessage name (evalState (failed ctx rule fs (everything `minus` sureOf x)) S.empty)]
  ]
  where
    rules = grammarRules g
    safe = map unLoc (grammarSafe g)
    (_, pass) = abstractions rules
    sureOf x = absSure (exprAbs pass x)
    callers = M.fromListWith (flip (++)) [(n, [s]) | r <- rules, s@(Site _ _ _ (ERef _ n _)) <- sites r]
    start = case (grammarStart g, rules) of
      (Just s, _) -> unLoc s
      (Nothing, r : _) -> ruleName r
      _ -> ""
    (direct, other, growing) = leftRecursion rules
    ctx =
      Ctx
        { ctxPass = pass
        , ctxCallers = callers
        , ctxEntries = S.fromList (start : map unLoc (grammarEntries g))
        , ctxRecovery = S.fromList [unLoc r | (_, r) <- grammarRecovers g]
        , ctxDirectLr = direct
        , ctxOtherLr = other
        , ctxGrowing = growing
        }

verdictMessage :: Text -> Verdict -> Maybe Text
verdictMessage name = \case
  Safe -> Nothing
  Unsafe why -> Just ("the label " <> name <> " may reject valid input: where it fails, " <> why)
  Unchecked why -> Just ("the label " <> name <> " cannot be checked: " <> why)

showLoc :: Loc -> Text
showLoc (Loc l c) = T.pack (show l) <> ":" <> T.pack (show c)

visit :: Text -> [Frame] -> Mode -> CharSet -> State Visited Verdict -> State Visited Verdict
visit rule fs mode k act = do
  let key = (rule, map frameKey fs, mode, k)
  seen <- gets (S.member key)
  if seen then pure Safe else modify' (S.insert key) >> act

allOf :: [State Visited Verdict] -> State Visited Verdict
allOf = foldr (\a acc -> a >>= \v -> if v == Safe then acc else pure v) (pure Safe)

-- The next character is in k at the start of an expression that failed.
failed :: Ctx -> Text -> [Frame] -> CharSet -> State Visited Verdict
failed ctx rule fs k = visit rule fs Failed k $ case fs of
  FSeq items j : FAlts alts i body : rest -> do
    let kAt m = before (take (j - m) (drop m items)) k
        growingAlt = body && S.member rule (ctxDirectLr ctx) && ctxGrowing ctx rule i
        later =
          [ (al, a)
          | (i', (al, a)) <- drop (i + 1) (zip [0 ..] alts)
          , not growingAlt || ctxGrowing ctx rule i'
          ]
        laterCheck (al, a) =
          let m = commonPrefix items a
           in if m > j
                then Safe
                else
                  if possible (seqAbs (ctxPass ctx) (drop m a)) `meets` kAt m
                    then Unsafe ("the alternative at " <> showLoc al <> " can match")
                    else Safe
    if body && S.member rule (ctxOtherLr ctx) && ctxGrowing ctx rule i
      then pure (Unchecked ("it is in a growing alternative of " <> rule <> ", which takes part in indirect or hidden left recursion"))
      else case foldr andAlso Safe (map laterCheck later) of
        Safe
          | growingAlt -> succeeded ctx rule [] (kAt 1)
          | otherwise -> failed ctx rule rest (kAt 0)
        v -> pure v
  FStar _ _ : rest -> succeeded ctx rule rest k
  FPlus _ _ : rest -> allOf [failed ctx rule rest k, succeeded ctx rule rest k]
  FOpt : rest -> succeeded ctx rule rest k
  FAnd : _ -> pure Safe
  FNot : _ -> pure Safe
  FLabel : rest -> failed ctx rule rest k
  FCapture : rest -> failed ctx rule rest k
  [] -> ruleFailed ctx rule k
  _ -> pure Safe
  where
    before prefix k' = let a = seqAbs (ctxPass ctx) prefix in absConsume a `union` (absEmpty a `intersect` k')

-- The next character is in k at the end of an expression that succeeded.
succeeded :: Ctx -> Text -> [Frame] -> CharSet -> State Visited Verdict
succeeded ctx rule fs k = visit rule fs Succeeded k $ case fs of
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
              [failed ctx rule (FSeq items (j + 1) : alts : rest) k | not (null after)]
                ++ [failed ctx rule (FSeq items m : alts : rest) everything | m <- [j + 2 .. length items - 1]]
                ++ [ended (absEmpty a `intersect` k) | absEmpty a `meets` k]
  FStar x l : rest -> again x l rest
  FPlus x l : rest -> again x l rest
  FOpt : rest -> succeeded ctx rule rest k
  FAnd : rest -> succeeded ctx rule rest everything
  FNot : rest -> failed ctx rule rest everything
  FLabel : rest -> succeeded ctx rule rest k
  FCapture : rest -> succeeded ctx rule rest k
  [] -> ruleSucceeded ctx rule k
  _ -> pure Safe
  where
    again x l rest
      | possible (exprAbs (ctxPass ctx) x) `meets` k = pure (Unsafe ("the repetition at " <> showLoc l <> " can continue"))
      | otherwise = succeeded ctx rule rest k

ruleFailed :: Ctx -> Text -> CharSet -> State Visited Verdict
ruleFailed ctx rule k
  | S.member rule (ctxRecovery ctx) = pure Safe
  | otherwise = allOf [failed ctx (siteRule s) (siteFrames s) k | s <- callersOf ctx rule]

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
-- and bindings.
commonPrefix :: [Item] -> [Item] -> Int
commonPrefix xs ys = length (takeWhile id (zipWith (\a b -> plain (itemExpr a) == plain (itemExpr b)) xs ys))
  where
    plain = \case
      ERef _ n args -> ERef noLoc n [Located noLoc (unLoc a) | a <- args]
      EGroup alts -> EGroup (map (map (\i -> Item noLoc Nothing (plain (itemExpr i)))) alts)
      EStar x -> EStar (plain x)
      EPlus x -> EPlus (plain x)
      EOpt x -> EOpt (plain x)
      EAnd x -> EAnd (plain x)
      ENot x -> ENot (plain x)
      ECapture x -> ECapture (plain x)
      ELabel _ x n -> ELabel noLoc (plain x) n
      EPred b (Located _ c) -> EPred b (Located noLoc c)
      e -> e
    noLoc = Loc 0 0

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
      _ -> []

-- Removing labels -----------------------------------------------------------------

-- | 'stripLabels', generating another module.
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
    , grammarEntries = grammarEntries g ++ [r | (_, r) <- grammarRecovers g, unLoc r `notElem` map unLoc (grammarEntries g)]
    , grammarRules = [r {ruleAlts = map alt (ruleAlts r)} | r <- grammarRules g]
    }
  where
    alt a = a {altItems = map item (altItems a)}
    item i = i {itemExpr = expr (itemExpr i)}
    expr = \case
      ELabel _ x _ -> expr x
      EGroup alts -> EGroup (map (map item) alts)
      EStar x -> EStar (expr x)
      EPlus x -> EPlus (expr x)
      EOpt x -> EOpt (expr x)
      EAnd x -> EAnd (expr x)
      ENot x -> ENot (expr x)
      ECapture x -> ECapture (expr x)
      e -> e
