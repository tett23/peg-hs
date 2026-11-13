-- Translate the result projection of choice with recovery disabled.
module Main (main) where

import Data.List (isPrefixOf, stripPrefix)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  [path] <- getArgs
  source <- lines <$> readFile path
  let body name = takeWhile (not . null) (dropWhile (not . isPrefixOf name) source)
  case body "runParser cfg " of
    "runParser cfg mkStore start input = runST $ do" : "  ctx <- newCtx cfg {cfgRecover = False} mkStore input" : _ -> pure ()
    _ -> die "strict parser must disable recovery"
  case body "saveErrors c" of
    ["saveErrors c", "  | cfgRecover (ctxConfig c) = Just <$> readSTRef (ctxErrors c)",
     "  | otherwise = pure Nothing"] -> pure ()
    _ -> die "unsupported saveErrors"
  case body "restoreErrors c =" of
    ["restoreErrors c = maybe (pure ()) (writeSTRef (ctxErrors c))"] -> pure ()
    _ -> die "unsupported restoreErrors"
  case body "choice ps =" of
    [start, "  saved <- saveErrors c", "  let go [] = pure Fail", "      go (p : rest) =",
     dispatch, "          r@Ok {} -> pure r", ordinary, "          r -> restoreErrors c saved >> pure r", "  go ps"]
      | start == "choice ps = P $ \\c i -> do", dispatch == "        unP p c i >>= \\case" -> do
          fallback <- case ordinary of
            "          Fail -> restoreErrors c saved >> go rest" -> pure "translatedChoice rest"
            "          Fail -> pure Fail" -> pure "some .fail"
            _ -> die "unsupported ordinary failure in choice"
          putStrLn "import EnvironmentEval\nnamespace PegHs.EnvironmentEval"
          putStrLn "def translatedChoice : List (Option Reply) → Option Reply"
          putStrLn "  | [] => some .fail"
          putStrLn "  | result :: rest => match result with"
          putStrLn ("    | some .fail => " ++ fallback)
          putStrLn "    | other => other"
    _ -> die "unsupported runtime choice"
  let emitLook name leanName setup =
        case splitAt (length setup) (body (name ++ " p =")) of
          (prefix, ["  case r of", ok, bad]) | prefix == setup -> do
            success <- branch "    Ok _ _ -> " ok
            failure <- branch "    _ -> " bad
            putStrLn ("def " ++ leanName ++ " (n : Nat) (env : Env) : Reply → Reply")
            putStrLn ("  | .ok _ _ => " ++ success)
            putStrLn ("  | _ => " ++ failure)
          _ -> die ("unsupported runtime " ++ name)
  emitLook "andP" "translatedAhead" ["andP p = P $ \\c i -> do", "  saved <- saveErrors c",
    "  r <- unP p c i", "  restoreErrors c saved"]
  emitLook "notP" "translatedNotAhead" ["notP p = P $ \\c i -> do", "  saved <- readSTRef (ctxFail c)",
    "  savedErrors <- saveErrors c", "  r <- unP p c i", "  writeSTRef (ctxFail c) saved",
    "  restoreErrors c savedErrors"]
  thrown <- case body "failed (Throw " of
    ["failed (Throw i l m) = Throw i l m", "failed _ = Fail"] -> pure ".throwLabel pos label msg"
    ["failed (Throw i l m) = Fail", "failed _ = Fail"] -> pure ".fail"
    _ -> die "unsupported failed result projection"
  case body "instance Monad (P " of
    ["instance Monad (P r s) where", "  {-# INLINE (>>=) #-}", "  P p >>= k =",
     "    P $ \\c i ->", "      p c i >>= \\case", success, "        bad -> pure (failed bad)"] -> do
      next <- case success of
        "        Ok j x -> unP (k x) c j" -> pure "next rest value"
        "        Ok j x -> unP (k x) c i" -> pure "next _origin value"
        _ -> die "unsupported continuation in parser bind"
      putStrLn "def translatedBind (_origin : Nat) (first : Option Reply) (next : Nat → Env → Option Reply) : Option Reply :="
      putStrLn "  match first with"
      putStrLn ("  | some (.ok rest value) => " ++ next)
      putStrLn "  | some .fail => some .fail"
      putStrLn ("  | some (.throwLabel pos label msg) => some (" ++ thrown ++ ")")
      putStrLn "  | none => none"
    _ -> die "unsupported parser bind"
  case body "optional p =" of
    ["optional p = P $ \\c i -> do", "  saved <- saveErrors c", "  unP p c i >>= \\case",
     "    Ok j x -> pure (Ok j (Just x))", empty, "    r -> restoreErrors c saved >> pure (failed r)"] -> do
      onFail <- case empty of
        "    Fail -> restoreErrors c saved >> pure (Ok i Nothing)" -> pure ".ok n absent"
        "    Fail -> restoreErrors c saved >> pure Fail" -> pure ".fail"
        _ -> die "unsupported optional failure"
      putStrLn "def translatedOptional (n : Nat) (absent : Env) : Reply → Reply"
      putStrLn "  | .ok rest value => .ok rest value"
      putStrLn ("  | .fail => " ++ onFail)
      putStrLn ("  | .throwLabel pos label msg => " ++ thrown)
    _ -> die "unsupported optional"
  let repeatGuard prefix suffix line = case stripPrefix prefix line of
        Just guard | guard == "k > j" ++ suffix -> pure "j < k"
                   | guard == "k >= j" ++ suffix -> pure "j ≤ k"
        _ -> die ("unsupported repetition guard: " ++ line)
      repeatBody name loop start finish okPrefix okSuffix stop = case body (name ++ " p =") of
        [header, definition, "        saved <- saveErrors c", dispatch, ok, thrownCase, stopped, entry]
          | header == name ++ " p = P $ \\c i ->", definition == loop, dispatch == "        unP p c j >>= \\case",
            thrownCase == "          Throw t l m -> restoreErrors c saved >> pure (Throw t l m)",
            stopped == "          _ -> restoreErrors c saved >> pure (Ok j " ++ stop ++ ")", entry == start -> do
              test <- repeatGuard okPrefix okSuffix ok
              putStrLn ("def " ++ finish ++ " (j k : Nat) : Prop := " ++ test)
        _ -> die ("unsupported repetition body: " ++ name)
  repeatBody "many" "  let go j acc = do" "   in go i []" "translatedManyProgress"
    "          Ok k x | " " -> go k (x : acc)" "(reverse acc)"
  -- repeatBody checked both the initial accumulator and the stopping
  -- branch of many above, including the order in which it returns values.
  putStrLn "def translatedManyInitial {α : Type} : List α := []"
  putStrLn "def translatedManyStop {α : Type} (acc : List α) : List α := acc.reverse"
  repeatBody "skipMany" "  let go j = do" "   in go i" "translatedSkipManyProgress"
    "          Ok k _ | " " -> go k" "()"
  case (body "labeled rawLabel =", body "labeledMessage rawLabel msg =") of
    (["labeled rawLabel = labeledWith plainRecovery rawLabel Nothing"],
     ["labeledMessage rawLabel msg = labeledWith plainRecovery rawLabel (Just (T.pack msg))"]) -> pure ()
    _ -> die "unsupported label wrappers"
  let labelSetup = ["labeledWith wrap rawLabel msg recovery p = P $ \\c i -> do",
        "  savedFail <- readSTRef (ctxFail c)", "  writeSTRef (ctxFail c) NoFailure",
        "  savedErrors <- saveErrors c", "  r <- unP p c i", "  local <- readSTRef (ctxFail c)",
        "  writeSTRef (ctxFail c) (mergeFailure savedFail local)", "  case r of", "    Fail -> do",
        "      restoreErrors c savedErrors", "      case recovery of", "        Just q | cfgRecover (ctxConfig c) ->"]
  case stripPrefix labelSetup (body "labeledWith wrap ") of
    Just rest -> case dropWhile (isPrefixOf "          ") rest of
      [onFail, "    _ -> pure r", "  where", "    l = T.pack rawLabel"] -> do
        failure <- case onFail of
          "        _ -> pure (Throw i l msg)" -> pure ".throwLabel n name msg"
          "        _ -> pure Fail" -> pure ".fail"
          _ -> die "unsupported strict label failure"
        putStrLn "def translatedLabel (n : Nat) (name : String) (msg : Option String) : Reply → Reply"
        putStrLn ("  | .fail => " ++ failure)
        putStrLn "  | other => other"
      _ -> die "unsupported strict label result"
    _ -> die "unsupported recovery guard in label"
  case (body "capture p =", body "slice t from to =") of
    (["capture p = P $ \\c i ->", "  unP p c i >>= \\case",
      "    Ok j _ -> pure (Ok j (slice (ctxInput c) i j))", "    bad -> pure (failed bad)"], [slice]) -> do
        count <- case slice of
          "slice t from to = TU.takeWord8 (to - from) (TU.dropWord8 from t)" -> pure "(stop - start)"
          "slice t from to = TU.takeWord8 to (TU.dropWord8 from t)" -> pure "stop"
          _ -> die "unsupported capture byte slice"
        putStrLn "def translatedCaptureBytes (input : ByteArray) (start stop : Nat) : ByteArray :="
        putStrLn ("  (input.extract start input.size).extract 0 " ++ count)
    _ -> die "unsupported capture"
  case body "predicate f =" of
    ["predicate f = P $ \\c i ->", condition] -> do
      test <- case condition of
        "  pure (if f (colAt c i) then Ok i () else Fail)" -> pure "test column"
        "  pure (if f (colAt c i) then Fail else Ok i ())" -> pure "!(test column)"
        _ -> die "unsupported semantic predicate branches"
      putStrLn "def translatedPredicate (test : Nat → Bool) (column n : Nat) (unitValue : Env) : Reply :="
      putStrLn ("  if " ++ test ++ " then .ok n unitValue else .fail")
    _ -> die "unsupported semantic predicate"
  putStrLn "end PegHs.EnvironmentEval"
  where
    branch prefix line = case stripPrefix prefix line of
      Just "pure (Ok i ())" -> pure ".ok n env"
      Just "pure Fail" -> pure ".fail"
      _ -> die ("unsupported lookahead branch: " ++ line)
