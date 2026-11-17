-- Translate the strict runtime of Peg.Runtime.Internal into Lean.
--
-- Each translated function is cut from the source at its defining equation
-- and ends at the next blank line. Every source line, or run of lines, must
-- be a key of that function's dictionary; the value is its Lean text. A line
-- that is not a key stops the translation. A deleted or reordered line is
-- translated as it stands, so the proofs, not this program, decide whether
-- the change is harmless. The vocabulary is defined in RuntimeCore.lean,
-- whose data types are compared with the source declarations below.
module Main (main) where

import Control.Monad (forM_, unless)
import Data.List (isPrefixOf, sortOn)
import Data.Ord (Down (..))
import System.Environment (getArgs)
import System.Exit (die)

type Rule = ([String], [String])

main :: IO ()
main = do
  [path] <- getArgs
  source <- lines <$> readFile path
  forM_ declarations $ \decl ->
    unless (decl `isInfixOfLines` source) $
      die ("runtime declaration changed: " ++ concat (take 1 decl))
  putStrLn "import RuntimeCore"
  putStrLn "namespace PegHs.RuntimeCore"
  putStrLn "noncomputable section"
  forM_ functions $ \(header, rules, epilogue) -> do
    body <- cut header source
    lean <- translate header rules body
    mapM_ putStrLn lean
    mapM_ putStrLn epilogue
    putStrLn ""
  putStrLn "end"
  putStrLn "end PegHs.RuntimeCore"

isInfixOfLines :: [String] -> [String] -> Bool
isInfixOfLines needle hay = any (needle `isPrefixOf`) (suffixes hay)
  where
    suffixes [] = [[]]
    suffixes xs@(_ : rest) = xs : suffixes rest

cut :: String -> [String] -> IO [String]
cut header source =
  case filter (header `isPrefixOf`) source of
    [_] -> pure (takeWhile (not . null) (dropWhile (not . (header `isPrefixOf`)) source))
    [] -> die ("missing runtime function: " ++ header)
    _ -> die ("ambiguous runtime function: " ++ header)

translate :: String -> [Rule] -> [String] -> IO [String]
translate name rules = go
  where
    ordered = sortOn (Down . length . fst) rules
    go [] = pure []
    go ls@(first : _) = case [(k, v) | (k, v) <- ordered, k `isPrefixOf` ls] of
      (k, v) : _ -> (v ++) <$> go (drop (length k) ls)
      [] -> die ("unsupported line in " ++ name ++ ": " ++ first)

one :: String -> String -> Rule
one h l = ([h], [l])

drop' :: String -> Rule
drop' h = ([h], [])

-- The source declarations that RuntimeCore.lean restates.
declarations :: [[String]]
declarations =
  [ [ "data Expected"
    , "  = -- | The display name of a rule, given by @%expect@ (ADR 0089). It"
    , "    -- replaces the terminals that the rule expected at its start."
    , "    ExpectedName !Text"
    , "  | -- | A literal, as written in the grammar (including its quotes)."
    , "    ExpectedLiteral !Text"
    , "  | -- | A character class, as written in the grammar."
    , "    ExpectedClass !Text"
    , "  | -- | Any single character."
    , "    ExpectedAny"
    , "  | -- | The end of the input."
    , "    ExpectedEnd"
    , "  deriving (Eq, Ord, Show)" ]
  , [ "data Failure", "  = NoFailure", "  | Failure !Int (Set Expected)", "  deriving (Eq, Show)" ]
  , [ "data Res a", "  = Ok !Int a", "  | Fail"
    , "  | -- | A labelled failure: the position where the labelled expression was"
    , "    -- tried, the label (ADR 0021) and its message (ADR 0089)."
    , "    Throw !Int !Text !(Maybe Text)" ]
  , [ "data ErrLog = ErrLog !Int [SyntaxError]" ]
  , [ "data ErrSlice = ErrSlice !Int [SyntaxError]" ]
  , [ "newtype P r s a = P {unP :: Ctx r s -> Int -> ST s (Res a)}" ]
  , [ "data Entry a = Entry !(Res a) !Failure !ErrSlice !IntSet" ]
  , [ "type Table s a = STRef s (IntMap (Entry a))" ]
  , [ "type ArgTable s k a = STRef s (IntMap (Map k (Entry a)))" ]
  , [ "emptyStats = Stats M.empty 0 M.empty" ]
  , [ "data Config = Config", "  { cfgMemo :: !Bool" ]
  , [ "  , cfgDiscard :: !Bool" ], [ "  , cfgDiscardAll :: !Bool" ], [ "  , cfgCount :: !Bool" ]
  , [ "  , cfgTabstop :: !Int" ], [ "  , cfgRecover :: !Bool" ]
  ]

functions :: [(String, [Rule], [String])]
functions =
  [ ("defaultConfig =",
      [ one "defaultConfig = Config {cfgMemo = True, cfgDiscard = True, cfgDiscardAll = False, cfgCount = False, cfgTabstop = 0, cfgRecover = False}"
            "def defaultConfig : Config := { cfgMemo := true, cfgDiscard := true, cfgDiscardAll := false, cfgCount := false, cfgTabstop := 0, cfgRecover := false }" ], [])
  , ("noErrors =", [ one "noErrors = ErrSlice 0 []" "def noErrors : ErrSlice := ErrSlice.ErrSlice 0 []" ], [])
  , ("failed (Throw",
      [ (["failed (Throw i l m) = Throw i l m"], ["def failed {α β : Type} : Res α → Res β", "  | Throw i l m => Throw i l m"])
      , one "failed _ = Fail" "  | _ => Fail" ], [])
  , ("mergeFailure NoFailure",
      [ (["mergeFailure NoFailure f = f"], ["def mergeFailure : Failure → Failure → Failure", "  | NoFailure, f => f"])
      , one "mergeFailure f NoFailure = f" "  | f, NoFailure => f"
      , one "mergeFailure a@(Failure i xs) b@(Failure j ys)" "  | a@(Failure.Failure i xs), b@(Failure.Failure j ys) =>"
      , one "  | i > j = a" "    if i > j then a"
      , one "  | i < j = b" "    else if i < j then b"
      , one "  | otherwise = Failure i (S.union xs ys)" "    else Failure.Failure i (S.union xs ys)" ], [])
  , ("instance Monad (P r s)",
      [ drop' "instance Monad (P r s) where"
      , drop' "  {-# INLINE (>>=) #-}"
      , one "  P p >>= k =" "def bindP {ρ σ α β : Type} (p : P ρ σ α) (k : α → P ρ σ β) : P ρ σ β :="
      , one "    P $ \\c i ->" "  fun c i =>"
      , one "      p c i >>= \\case" "    p c i >>= fun"
      , one "        Ok j x -> unP (k x) c j" "      | Ok j x => unP (k x) c j"
      , one "        bad -> pure (failed bad)" "      | bad => pure (failed bad)" ], [])
  , ("instance Functor (P r s)",
      [ drop' "instance Functor (P r s) where"
      , drop' "  {-# INLINE fmap #-}"
      , one "  fmap f (P p) =" "def fmapP {ρ σ α β : Type} (f : α → β) (p : P ρ σ α) : P ρ σ β :="
      , one "    P $ \\c i ->" "  fun c i =>"
      , one "      p c i >>= \\case" "    p c i >>= fun"
      , one "        Ok j x -> pure (Ok j (f x))" "      | Ok j x => pure (Ok j (f x))"
      , one "        bad -> pure (failed bad)" "      | bad => pure (failed bad)" ], [])
  , ("instance Applicative (P r s)",
      [ drop' "instance Applicative (P r s) where"
      , drop' "  {-# INLINE pure #-}"
      , one "  pure x = P $ \\_ i -> pure (Ok i x)" "def pureP {ρ σ α : Type} (x : α) : P ρ σ α := fun _ i => pure (Ok i x)"
      , drop' "  {-# INLINE (<*>) #-}"
      -- Control.Monad.ap: do { f <- mf; x <- mx; return (f x) }.
      , (["  (<*>) = ap"], [ "def apP {ρ σ α β : Type} (pf : P ρ σ (α → β)) (px : P ρ σ α) : P ρ σ β :="
                           , "  bindP pf fun f => bindP px fun x => pureP (f x)" ]) ], [])
  , ("saveErrors c",
      [ one "saveErrors c" "def saveErrors {ρ σ : Type} (c : Ctx ρ) : ST σ (Option ErrLog) :="
      , one "  | cfgRecover (ctxConfig c) = Just <$> readSTRef (ctxErrors c)" "  if cfgRecover (ctxConfig c) then some <$> readSTRef (ctxErrors c)"
      , one "  | otherwise = pure Nothing" "  else pure none" ], [])
  , ("restoreErrors c =",
      [ (["restoreErrors c = maybe (pure ()) (writeSTRef (ctxErrors c))"],
         [ "def restoreErrors {ρ σ : Type} (c : Ctx ρ) : Option ErrLog → ST σ Unit :="
         , "  maybe (pure ()) (writeSTRef (ctxErrors c))" ]) ], [])
  , ("mergeFail ctx f =",
      [ (["mergeFail ctx f = modifySTRef' (ctxFail ctx) (`mergeFailure` f)"],
         [ "def mergeFail {ρ σ : Type} (ctx : Ctx ρ) (f : Failure) : ST σ Unit :="
         , "  modifySTRef' (ctxFail ctx) (fun x => mergeFailure x f)" ]) ], [])
  , ("failAt ctx i e =",
      [ one "failAt ctx i e = do" "def failAt {ρ σ α : Type} (ctx : Ctx ρ) (i : Nat) (e : Expected) : ST σ (Res α) := do"
      , drop' "  -- A failure before the farthest one changes nothing: skip building it."
      , one "  cur <- readSTRef (ctxFail ctx)" "  let cur ← readSTRef (ctxFail ctx)"
      -- The guard falls through to the wildcard alternative.
      , ([ "  case cur of", "    Failure j _ | j > i -> pure ()"
         , "    _ -> writeSTRef (ctxFail ctx) $! mergeFailure cur (Failure i (S.singleton e))" ],
         [ "  match cur with"
         , "    | Failure.Failure j _ =>"
         , "      if j > i then pure () else writeSTRef (ctxFail ctx) (mergeFailure cur (Failure.Failure i (S.singleton e)))"
         , "    | _ => writeSTRef (ctxFail ctx) (mergeFailure cur (Failure.Failure i (S.singleton e)))" ])
      , one "  pure Fail" "  pure Fail" ], [])
  , ("currentError ctx failLabel msg =",
      [ one "currentError ctx failLabel msg =" "def currentError {ρ σ : Type} (ctx : Ctx ρ) (failLabel msg : Option Text) : ST σ ParseError :="
      , one "  readSTRef (ctxFail ctx) >>= \\case" "  readSTRef (ctxFail ctx) >>= fun"
      , one "    NoFailure -> pure (ParseError (posAt ctx 0) S.empty failLabel msg)" "    | NoFailure => pure (ParseError.mk (posAt ctx 0) S.empty failLabel msg)"
      , one "    Failure i xs -> pure (ParseError (posAt ctx i) xs failLabel msg)" "    | Failure.Failure i xs => pure (ParseError.mk (posAt ctx i) xs failLabel msg)" ], [])
  , ("newCtx cfg mkStore input =",
      [ one "newCtx cfg mkStore input = do" "def newCtx {ρ σ : Type} (cfg : Config) (mkStore : ST σ ρ) (input : Text) : ST σ (Ctx ρ) := do"
      , one "  st <- mkStore" "  let st ← mkStore"
      , one "  fref <- newSTRef NoFailure" "  let _fref ← newFailRef NoFailure"
      , one "  errs <- newSTRef (ErrLog 0 [])" "  let _errs ← newErrorsRef (ErrLog.ErrLog 0 [])"
      , one "  logs <- newSTRef []" "  let _logs ← newLogsRef []"
      , one "  deps <- newSTRef IS.empty" "  let _deps ← newDepsRef IS.empty"
      , one "  depth <- newSTRef 0" "  let _depth ← newDepthRef 0"
      , one "  stats <- newSTRef emptyStats" "  let _stats ← newStatsRef emptyStats"
      , one "  pure" "  pure"
      , drop' "    Ctx"
      , one "      { ctxInput = input" "      { ctxInput := input"
      , one "      , ctxLen = TU.lengthWord8 input" "        ctxLen := TU.lengthWord8 input"
      , one "      , ctxStore = st" "        ctxStore := st"
      -- R1: the refs are the fixed fields allocated above.
      , drop' "      , ctxFail = fref", drop' "      , ctxErrors = errs", drop' "      , ctxDeps = deps"
      , drop' "      , ctxDepth = depth", drop' "      , ctxLogs = logs", drop' "      , ctxStats = stats"
      , one "      , ctxConfig = cfg" "        ctxConfig := cfg"
      -- R4: positions are kept as byte offsets.
      , drop' "      , ctxLines = lineIndex input"
      , one "      }" "      }" ], [])
  , ("runParser cfg mkStore start input =",
      [ (["runParser cfg mkStore start input = runST $ do"],
         [ "def runParser {ρ σ α : Type} (cfg : Config) (mkStore : ST σ ρ) (start : P ρ σ α) (input : Text) :"
         , "    World σ → Option (Except ParseError α × Stats) := runST <| do" ])
      , one "  ctx <- newCtx cfg {cfgRecover = False} mkStore input" "  let ctx ← newCtx { cfg with cfgRecover := false } mkStore input"
      , one "  r <- unP start ctx 0" "  let r ← unP start ctx 0"
      , one "  res <- case r of" "  let res ← match r with"
      , (["    Ok j x | j == ctxLen ctx -> pure (Right x)", "    Ok j _ -> do"],
         ["    | Ok j x => if j == ctxLen ctx then pure (Except.ok x) else do"])
      , one "      mergeFail ctx (Failure j (S.singleton ExpectedEnd))" "      mergeFail ctx (Failure.Failure j (S.singleton ExpectedEnd))"
      , one "      Left <$> currentError ctx Nothing Nothing" "      Except.error <$> currentError ctx none none"
      , one "    Throw _ l m -> Left <$> currentError ctx (Just l) m" "    | Throw _ l m => Except.error <$> currentError ctx (some l) m"
      , one "    Fail -> Left <$> currentError ctx Nothing Nothing" "    | Fail => Except.error <$> currentError ctx none none"
      , one "  s <- readSTRef (ctxStats ctx)" "  let s ← readSTRef (ctxStats ctx)"
      , one "  pure (res, s)" "  pure (res, s)" ], [])
  , ("lit s orig =",
      [ one "lit s orig = P $ \\c i ->" "def lit {ρ σ : Type} (s orig : String) : P ρ σ Unit := fun c i =>"
      , one "  if matchesAt (ctxInput c) i" "  if matchesAt (ctxInput c) i"
      , one "    then pure (Ok (i + n) ())" "    then pure (Ok (i + n) ())"
      , one "    else failAt c i expected" "    else failAt c i expected"
      , one "  where" "  where"
      -- R3: the packed literal is its UTF-8 bytes at offset 0.
      , (["    Text tarr toff n = T.pack s"],
         [ "    tarr : ByteArray := (T.pack s).toUTF8"
         , "    toff : Nat := 0"
         , "    n : Nat := TU.lengthWord8 (T.pack s)" ])
      , one "    expected = ExpectedLiteral (T.pack orig)" "    expected : Expected := ExpectedLiteral (T.pack orig)"
      , drop' "    -- Compare the bytes in place, without slicing the input."
      -- R3: the input's array, offset and length; go is lifted to a sibling.
      , one "    matchesAt (Text arr off len) i = i + n <= len && go 0"
            "    matchesAt (input : Text) (i : Nat) : Bool := decide (i + n ≤ TU.lengthWord8 input) && go input.toUTF8 0 i 0"
      , drop' "      where"
      , one "        go k" "    go (arr : ByteArray) (off i k : Nat) : Bool :="
      , one "          | k == n = True" "      if k == n then true"
      -- go starts at 0 and stops at n, so k < n holds whenever this guard is
      -- tried. Lean needs it as evidence of termination; the added else
      -- branch is unreachable from go 0.
      , one "          | TA.unsafeIndex arr (off + i + k) == TA.unsafeIndex tarr (toff + k) = go (k + 1)"
            "      else if h : k < n then if TA.unsafeIndex arr (off + i + k) == TA.unsafeIndex tarr (toff + k) then go arr off i (k + 1)"
      , ( ["          | otherwise = False"], [ "        else false", "      else false", "    termination_by lit.n s - k" ]) ], [])
  , ("cls ranges orig =",
      [ one "cls ranges orig = P $ \\c i ->" "def cls {ρ σ : Type} (ranges : List (Char × Char)) (orig : String) : P ρ σ Unit := fun c i =>"
      , one "  if i < ctxLen c" "  if i < ctxLen c"
      , one "    then" "    then"
      , one "      let TU.Iter ch d = TU.iter (ctxInput c) i" "      let ⟨ch, d⟩ := TU.iter (ctxInput c) i"
      , one "       in if any (\\(a, b) -> a <= ch && ch <= b) ranges" "      if ranges.any (fun (a, b) => decide (a ≤ ch) && decide (ch ≤ b))"
      , one "            then pure (Ok (i + d) ())" "            then pure (Ok (i + d) ())"
      , one "            else failAt c i expected" "            else failAt c i expected"
      , one "    else failAt c i expected" "    else failAt c i expected"
      , one "  where" "  where"
      , one "    expected = ExpectedClass (T.pack orig)" "    expected : Expected := ExpectedClass (T.pack orig)" ], [])
  , ("anyChar = ",
      [ one "anyChar = P $ \\c i ->" "def anyChar {ρ σ : Type} : P ρ σ Unit := fun c i =>"
      , one "  if i < ctxLen c" "  if i < ctxLen c"
      , one "    then let TU.Iter _ d = TU.iter (ctxInput c) i in pure (Ok (i + d) ())" "    then let ⟨_, d⟩ := TU.iter (ctxInput c) i; pure (Ok (i + d) ())"
      , one "    else failAt c i ExpectedAny" "    else failAt c i ExpectedAny" ], [])
  , ("choice ps =",
      [ one "choice ps = P $ \\c i -> do" "def choice {ρ σ α : Type} (ps : List (P ρ σ α)) : P ρ σ α := fun c i => do"
      , one "  saved <- saveErrors c" "  let saved ← saveErrors c"
      , (["  let go [] = pure Fail"], ["  let rec go : List (P ρ σ α) → ST σ (Res α)", "    | [] => pure Fail"])
      , one "      go (p : rest) =" "    | p :: rest =>"
      , one "        unP p c i >>= \\case" "        unP p c i >>= fun"
      , one "          r@Ok {} -> pure r" "          | r@(Ok ..) => pure r"
      , one "          Fail -> restoreErrors c saved >> go rest" "          | Fail => restoreErrors c saved >>= fun _ => go rest"
      , one "          r -> restoreErrors c saved >> pure r" "          | r => restoreErrors c saved >>= fun _ => pure r"
      , one "  go ps" "  go ps" ], [])
  , ("many p =",
      -- The loop is lifted to a top-level definition; its guard falls
      -- through to the wildcard alternative.
      [ ([ "many p = P $ \\c i ->"
         , "  let go j acc = do"
         , "        saved <- saveErrors c"
         , "        unP p c j >>= \\case"
         , "          Ok k x | k > j -> go k (x : acc)"
         , "          Throw t l m -> restoreErrors c saved >> pure (Throw t l m)"
         , "          _ -> restoreErrors c saved >> pure (Ok j (reverse acc))"
         , "   in go i []" ],
         [ "def manyGo {ρ σ α : Type} (p : P ρ σ α) (c : Ctx ρ) (j : Nat) (acc : List α) : ST σ (Res (List α)) := do"
         , "  let saved ← saveErrors c"
         , "  unP p c j >>= fun"
         , "    | Ok k x => if k > j then manyGo p c k (x :: acc) else restoreErrors c saved >>= fun _ => pure (Ok j acc.reverse)"
         , "    | Throw t l m => restoreErrors c saved >>= fun _ => pure (Throw t l m)"
         , "    | _ => restoreErrors c saved >>= fun _ => pure (Ok j acc.reverse)"
         , "partial_fixpoint"
         , ""
         , "def many {ρ σ α : Type} (p : P ρ σ α) : P ρ σ (List α) := fun c i => manyGo p c i []" ]) ], [])
  , ("skipMany p =",
      [ ([ "skipMany p = P $ \\c i ->"
         , "  let go j = do"
         , "        saved <- saveErrors c"
         , "        unP p c j >>= \\case"
         , "          Ok k _ | k > j -> go k"
         , "          Throw t l m -> restoreErrors c saved >> pure (Throw t l m)"
         , "          _ -> restoreErrors c saved >> pure (Ok j ())"
         , "   in go i" ],
         [ "def skipManyGo {ρ σ α : Type} (p : P ρ σ α) (c : Ctx ρ) (j : Nat) : ST σ (Res Unit) := do"
         , "  let saved ← saveErrors c"
         , "  unP p c j >>= fun"
         , "    | Ok k _ => if k > j then skipManyGo p c k else restoreErrors c saved >>= fun _ => pure (Ok j ())"
         , "    | Throw t l m => restoreErrors c saved >>= fun _ => pure (Throw t l m)"
         , "    | _ => restoreErrors c saved >>= fun _ => pure (Ok j ())"
         , "partial_fixpoint"
         , ""
         , "def skipMany {ρ σ α : Type} (p : P ρ σ α) : P ρ σ Unit := fun c i => skipManyGo p c i" ]) ], [])
  , ("many1 p =",
      [ (["many1 p = (:) <$> p <*> many p"],
         ["def many1 {ρ σ α : Type} (p : P ρ σ α) : P ρ σ (List α) := apP (fmapP List.cons p) (many p)"]) ], [])
  , ("skipMany1 p =",
      [ (["skipMany1 p = p >> skipMany p"],
         ["def skipMany1 {ρ σ α : Type} (p : P ρ σ α) : P ρ σ Unit := bindP p fun _ => skipMany p"]) ], [])
  , ("optional p =",
      [ one "optional p = P $ \\c i -> do" "def optional {ρ σ α : Type} (p : P ρ σ α) : P ρ σ (Option α) := fun c i => do"
      , one "  saved <- saveErrors c" "  let saved ← saveErrors c"
      , one "  unP p c i >>= \\case" "  unP p c i >>= fun"
      , one "    Ok j x -> pure (Ok j (Just x))" "    | Ok j x => pure (Ok j (some x))"
      , one "    Fail -> restoreErrors c saved >> pure (Ok i Nothing)" "    | Fail => restoreErrors c saved >>= fun _ => pure (Ok i none)"
      , one "    r -> restoreErrors c saved >> pure (failed r)" "    | r => restoreErrors c saved >>= fun _ => pure (failed r)" ], [])
  , ("skipOptional p =",
      [ (["skipOptional p = () <$ optional p"],
         ["def skipOptional {ρ σ α : Type} (p : P ρ σ α) : P ρ σ Unit := fmapP (fun _ => ()) (optional p)"]) ], [])
  , ("andP p =",
      [ one "andP p = P $ \\c i -> do" "def andP {ρ σ α : Type} (p : P ρ σ α) : P ρ σ Unit := fun c i => do"
      , one "  saved <- saveErrors c" "  let saved ← saveErrors c"
      , one "  r <- unP p c i" "  let r ← unP p c i"
      , one "  restoreErrors c saved" "  restoreErrors c saved"
      , one "  case r of" "  match r with"
      , one "    Ok _ _ -> pure (Ok i ())" "    | Ok _ _ => pure (Ok i ())"
      , one "    _ -> pure Fail" "    | _ => pure Fail" ], [])
  , ("notP p =",
      [ one "notP p = P $ \\c i -> do" "def notP {ρ σ α : Type} (p : P ρ σ α) : P ρ σ Unit := fun c i => do"
      , one "  saved <- readSTRef (ctxFail c)" "  let saved ← readSTRef (ctxFail c)"
      , one "  savedErrors <- saveErrors c" "  let savedErrors ← saveErrors c"
      , one "  r <- unP p c i" "  let r ← unP p c i"
      , one "  writeSTRef (ctxFail c) saved" "  writeSTRef (ctxFail c) saved"
      , one "  restoreErrors c savedErrors" "  restoreErrors c savedErrors"
      , one "  case r of" "  match r with"
      , one "    Ok _ _ -> pure Fail" "    | Ok _ _ => pure Fail"
      , one "    _ -> pure (Ok i ())" "    | _ => pure (Ok i ())" ], [])
  , ("countEval c name i =",
      [ one "countEval c name i =" "def countEval {ρ σ : Type} (c : Ctx ρ) (name : Text) (i : Nat) : ST σ Unit :="
      , one "  when (cfgCount (ctxConfig c)) $" "  when (cfgCount (ctxConfig c)) <|"
      , one "    modifySTRef' (ctxStats c) $ \\st ->" "    modifySTRef' (ctxStats c) <| fun st =>"
      , one "      st {statsEvaluations = M.insertWith (+) (name, i) 1 (statsEvaluations st)}"
            "      { st with statsEvaluations := M.insertWith (· + ·) (name, i) 1 (statsEvaluations st) }" ], [])
  , ("bumpEntries c name d =",
      [ one "bumpEntries c name d =" "def bumpEntries {ρ σ : Type} (c : Ctx ρ) (name : Text) (d : Int) : ST σ Unit :="
      , one "  when (cfgCount (ctxConfig c)) $" "  when (cfgCount (ctxConfig c)) <|"
      , one "    modifySTRef' (ctxStats c) $ \\st ->" "    modifySTRef' (ctxStats c) <| fun st =>"
      , one "      st" "      { st with"
      , one "        { statsMemoEntries = statsMemoEntries st + d" "        statsMemoEntries := statsMemoEntries st + d"
      , one "        , statsEntriesByRule = M.insertWith (+) name d (statsEntriesByRule st)" "        statsEntriesByRule := M.insertWith (· + ·) name d (statsEntriesByRule st)"
      , one "        }" "      }" ], [])
  , ("newErrors _ Nothing",
      [ (["newErrors _ Nothing = pure noErrors"], ["def newErrors {ρ σ : Type} : Ctx ρ → Option ErrLog → ST σ ErrSlice", "  | _, none => pure noErrors"])
      , one "newErrors c (Just (ErrLog old _)) = do" "  | c, some (ErrLog.ErrLog old _) => do"
      , one "  ErrLog now xs <- readSTRef (ctxErrors c)" "    let ⟨now, xs⟩ ← readSTRef (ctxErrors c)"
      , one "  pure (ErrSlice (now - old) xs)" "    pure (ErrSlice.ErrSlice (now - old) xs)" ], [])
  , ("appendSlice _ (ErrSlice 0 _)",
      [ (["appendSlice _ (ErrSlice 0 _) = pure ()"], ["def appendSlice {ρ σ : Type} : Ctx ρ → ErrSlice → ST σ Unit", "  | _, ErrSlice.ErrSlice 0 _ => pure ()"])
      , one "appendSlice c (ErrSlice k xs) = modifySTRef' (ctxErrors c) (\\(ErrLog n ys) -> ErrLog (n + k) (take k xs ++ ys))"
            "  | c, ErrSlice.ErrSlice k xs => modifySTRef' (ctxErrors c) (fun | ErrLog.ErrLog n ys => ErrLog.ErrLog (n + k) (xs.take k ++ ys))" ], [])
  , ("evalBody c name i body =",
      [ one "evalBody c name i body = do" "def evalBody {ρ σ α : Type} (c : Ctx ρ) (name : Text) (i : Nat) (body : P ρ σ α) : ST σ (Res α × Failure × ErrSlice × IntSet) := do"
      , one "  countEval c name i" "  countEval c name i"
      , one "  saved <- readSTRef (ctxFail c)" "  let saved ← readSTRef (ctxFail c)"
      , one "  writeSTRef (ctxFail c) NoFailure" "  writeSTRef (ctxFail c) NoFailure"
      , one "  savedDeps <- readSTRef (ctxDeps c)" "  let savedDeps ← readSTRef (ctxDeps c)"
      , one "  writeSTRef (ctxDeps c) IS.empty" "  writeSTRef (ctxDeps c) IS.empty"
      , one "  before <- saveErrors c" "  let before ← saveErrors c"
      , one "  r <- unP body c i" "  let r ← unP body c i"
      , one "  f <- readSTRef (ctxFail c)" "  let f ← readSTRef (ctxFail c)"
      , one "  writeSTRef (ctxFail c) (mergeFailure saved f)" "  writeSTRef (ctxFail c) (mergeFailure saved f)"
      , one "  d <- readSTRef (ctxDeps c)" "  let d ← readSTRef (ctxDeps c)"
      , one "  writeSTRef (ctxDeps c) (IS.union savedDeps d)" "  writeSTRef (ctxDeps c) (IS.union savedDeps d)"
      , one "  new <- case r of" "  let new ← match r with"
      , one "    Ok {} -> newErrors c before" "    | Ok .. => newErrors c before"
      , one "    _ -> noErrors <$ restoreErrors c before" "    | _ => (fun _ => noErrors) <$> restoreErrors c before"
      , one "  pure (r, f, new, d)" "  pure (r, f, new, d)" ], [])
  , ("replay c (Entry r f errs d) =",
      [ (["replay c (Entry r f errs d) = do"],
         [ "def replay {ρ σ α : Type} (c : Ctx ρ) (entry : Entry α) : ST σ (Res α) := do"
         , "  let ⟨r, f, errs, d⟩ := entry" ])
      , one "  mergeFail c f" "  mergeFail c f"
      , one "  when (not (IS.null d)) (modifySTRef' (ctxDeps c) (IS.union d))" "  when (not (IS.null d)) (modifySTRef' (ctxDeps c) (IS.union d))"
      , one "  case r of" "  match r with"
      , one "    Ok {} -> appendSlice c errs" "    | Ok .. => appendSlice c errs"
      , one "    _ -> pure ()" "    | _ => pure ()"
      , one "  pure r" "  pure r" ], [])
  , ("logUndo c deps undo =",
      [ one "logUndo c deps undo =" "def logUndo {ρ σ : Type} (c : Ctx ρ) (deps : IntSet) (_undo : ST σ Unit) : ST σ Unit :="
      , one "  when (not (IS.null deps) || cfgDiscardAll (ctxConfig c)) $" "  when (not (IS.null deps) || cfgDiscardAll (ctxConfig c)) <|"
      , one "    readSTRef (ctxLogs c) >>= \\case" "    readSTRef (ctxLogs c) >>= fun"
      -- R5: the undo action is erased.
      , one "      l : ls -> writeSTRef (ctxLogs c) (((deps, undo) : l) : ls)" "      | l :: ls => writeSTRef (ctxLogs c) (((deps, ()) :: l) :: ls)"
      , one "      [] -> pure ()" "      | [] => pure ()" ], [])
  , ("memo sel rawName body =",
      [ one "memo sel rawName body = P $ \\c i ->" "def memo {ρ σ α : Type} (sel : ρ → Table σ α) (rawName : String) (body : P ρ σ α) : P ρ σ α := fun c i =>"
      , one "  if not (cfgMemo (ctxConfig c))" "  if not (cfgMemo (ctxConfig c))"
      , one "    then (\\(r, _, _, _) -> r) <$> evalBody c name i body" "    then (fun (r, _, _, _) => r) <$> evalBody c name i body"
      , one "    else do" "    else do"
      , one "      let t = sel (ctxStore c)" "      let t := sel (ctxStore c)"
      , one "      IM.lookup i <$> readSTRef t >>= \\case" "      IM.lookup i <$> readSTRef t >>= fun"
      , one "        Just e -> replay c e" "        | some e => replay c e"
      , one "        Nothing -> do" "        | none => do"
      , one "          (r, f, errs, d) <- evalBody c name i body" "          let (r, f, errs, d) ← evalBody c name i body"
      , one "          modifySTRef' t (IM.insert i (Entry r f errs d))" "          modifySTRef' t (IM.insert i (Entry.Entry r f errs d))"
      , one "          bumpEntries c name 1" "          bumpEntries c name 1"
      , one "          logUndo c d (modifySTRef' t (IM.delete i) >> bumpEntries c name (-1))" "          logUndo c d (modifySTRef' t (IM.delete i) >>= fun _ => bumpEntries c name (-1))"
      , one "          pure r" "          pure r"
      , one "  where" "  where"
      , one "    name = T.pack rawName" "    name : Text := T.pack rawName" ], [])
  , ("memoArg sel rawName k body =",
      [ one "memoArg sel rawName k body = P $ \\c i ->" "def memoArg {ρ σ κ α : Type} [DecidableEq κ] (sel : ρ → ArgTable σ κ α) (rawName : String) (k : κ) (body : P ρ σ α) : P ρ σ α := fun c i =>"
      , one "  if not (cfgMemo (ctxConfig c))" "  if not (cfgMemo (ctxConfig c))"
      , one "    then (\\(r, _, _, _) -> r) <$> evalBody c name i body" "    then (fun (r, _, _, _) => r) <$> evalBody c name i body"
      , one "    else do" "    else do"
      , one "      let t = sel (ctxStore c)" "      let t := sel (ctxStore c)"
      , one "      (IM.lookup i <$> readSTRef t) >>= \\m -> case m >>= M.lookup k of" "      (IM.lookup i <$> readSTRef t) >>= fun m => match m >>= M.lookup k with"
      , one "        Just e -> replay c e" "        | some e => replay c e"
      , one "        Nothing -> do" "        | none => do"
      , one "          (r, f, errs, d) <- evalBody c name i body" "          let (r, f, errs, d) ← evalBody c name i body"
      , one "          modifySTRef' t (IM.insertWith M.union i (M.singleton k (Entry r f errs d)))" "          modifySTRef' t (IM.insertWith M.union i (M.singleton k (Entry.Entry r f errs d)))"
      , one "          bumpEntries c name 1" "          bumpEntries c name 1"
      , one "          logUndo c d (modifySTRef' t (IM.adjust (M.delete k) i) >> bumpEntries c name (-1))" "          logUndo c d (modifySTRef' t (IM.adjust (M.delete k) i) >>= fun _ => bumpEntries c name (-1))"
      , one "          pure r" "          pure r"
      , one "  where" "  where"
      , one "    name = T.pack rawName" "    name : Text := T.pack rawName" ], [])
  , ("nomemo rawName body =",
      [ one "nomemo rawName body = P $ \\c i -> (\\(r, _, _, _) -> r) <$> evalBody c name i body"
            "def nomemo {ρ σ α : Type} (rawName : String) (body : P ρ σ α) : P ρ σ α := fun c i => (fun (r, _, _, _) => r) <$> evalBody c name i body"
      , one "  where" "  where"
      , one "    name = T.pack rawName" "    name : Text := T.pack rawName" ], [])
  , ("plainRecovery _ _ v =",
      [ one "plainRecovery _ _ v = v" "def plainRecovery {α : Type} (_ _ : Nat) (v : α) : α := v" ], [])
  , ("labeledWith wrap rawLabel msg recovery p =",
      [ one "labeledWith wrap rawLabel msg recovery p = P $ \\c i -> do"
            "def labeledWith {ρ σ α : Type} (wrap : Nat → Nat → α → α) (rawLabel : String) (msg : Option Text) (recovery : Option (P ρ σ α)) (p : P ρ σ α) : P ρ σ α := fun c i => do"
      , one "  savedFail <- readSTRef (ctxFail c)" "  let savedFail ← readSTRef (ctxFail c)"
      , one "  writeSTRef (ctxFail c) NoFailure" "  writeSTRef (ctxFail c) NoFailure"
      , one "  savedErrors <- saveErrors c" "  let savedErrors ← saveErrors c"
      , one "  r <- unP p c i" "  let r ← unP p c i"
      -- `local` is a Lean keyword.
      , one "  local <- readSTRef (ctxFail c)" "  let loc ← readSTRef (ctxFail c)"
      , one "  writeSTRef (ctxFail c) (mergeFailure savedFail local)" "  writeSTRef (ctxFail c) (mergeFailure savedFail loc)"
      , one "  case r of" "  match r with"
      , one "    Fail -> do" "    | Fail => do"
      , one "      restoreErrors c savedErrors" "      restoreErrors c savedErrors"
      , one "      case recovery of" "      match recovery with"
      -- The guard falls through to the wildcard alternative.
      , (["        Just q | cfgRecover (ctxConfig c) ->"], ["        | some q =>", "          if cfgRecover (ctxConfig c) then"])
      , one "          unP q c i >>= \\case" "          unP q c i >>= fun"
      , one "            Ok j v -> do" "            | Ok j v => do"
      , one "              let expected = case local of" "              let expected := match loc with"
      , one "                    Failure _ xs -> xs" "                    | Failure.Failure _ xs => xs"
      , one "                    NoFailure -> S.empty" "                    | NoFailure => S.empty"
      , one "              modifySTRef' (ctxErrors c) (\\(ErrLog n xs) -> ErrLog (n + 1) (SyntaxError (Just l) (i, j) (posAt c i) expected msg : xs))"
            "              modifySTRef' (ctxErrors c) (fun | ErrLog.ErrLog n xs => ErrLog.ErrLog (n + 1) (SyntaxError.mk (some l) (i, j) (posAt c i) expected msg :: xs))"
      , one "              pure (Ok j (wrap i j v))" "              pure (Ok j (wrap i j v))"
      , one "            _ -> restoreErrors c savedErrors >> pure (Throw i l msg)" "            | _ => restoreErrors c savedErrors >>= fun _ => pure (Throw i l msg)"
      , (["        _ -> pure (Throw i l msg)"], ["          else pure (Throw i l msg)", "        | _ => pure (Throw i l msg)"])
      , one "    _ -> pure r" "    | _ => pure r"
      , one "  where" "  where"
      , one "    l = T.pack rawLabel" "    l : Text := T.pack rawLabel" ], [])
  , ("labeled rawLabel =",
      [ (["labeled rawLabel = labeledWith plainRecovery rawLabel Nothing"],
         [ "def labeled {ρ σ α : Type} (rawLabel : String) : Option (P ρ σ α) → P ρ σ α → P ρ σ α :="
         , "  labeledWith plainRecovery rawLabel none" ]) ], [])
  , ("labeledMessage rawLabel msg =",
      [ (["labeledMessage rawLabel msg = labeledWith plainRecovery rawLabel (Just (T.pack msg))"],
         [ "def labeledMessage {ρ σ α : Type} (rawLabel msg : String) : Option (P ρ σ α) → P ρ σ α → P ρ σ α :="
         , "  labeledWith plainRecovery rawLabel (some (T.pack msg))" ]) ], [])
  , ("expecting rawName p =",
      [ one "expecting rawName p = P $ \\c i -> do" "def expecting {ρ σ α : Type} (rawName : String) (p : P ρ σ α) : P ρ σ α := fun c i => do"
      , one "  saved <- readSTRef (ctxFail c)" "  let saved ← readSTRef (ctxFail c)"
      , one "  writeSTRef (ctxFail c) NoFailure" "  writeSTRef (ctxFail c) NoFailure"
      , one "  r <- unP p c i" "  let r ← unP p c i"
      , one "  local <- readSTRef (ctxFail c)" "  let loc ← readSTRef (ctxFail c)"
      , ([ "  let renamed = case local of"
         , "        Failure j _ | j == i -> Failure i (S.singleton (ExpectedName name))"
         , "        f -> f" ],
         [ "  let renamed := match loc with"
         , "        | Failure.Failure j xs => if j == i then Failure.Failure i (S.singleton (ExpectedName name)) else Failure.Failure j xs"
         , "        | f => f" ])
      , one "  writeSTRef (ctxFail c) (mergeFailure saved renamed)" "  writeSTRef (ctxFail c) (mergeFailure saved renamed)"
      , one "  pure r" "  pure r"
      , one "  where" "  where"
      , one "    name = T.pack rawName" "    name : Text := T.pack rawName" ], [])
  ]
