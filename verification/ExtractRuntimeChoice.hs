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
  putStrLn "end PegHs.EnvironmentEval"
  where
    branch prefix line = case stripPrefix prefix line of
      Just "pure (Ok i ())" -> pure ".ok n env"
      Just "pure Fail" -> pure ".fail"
      _ -> die ("unsupported lookahead branch: " ++ line)
