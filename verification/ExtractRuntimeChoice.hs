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
  putStrLn "end PegHs.EnvironmentEval"
  where
    branch prefix line = case stripPrefix prefix line of
      Just "pure (Ok i ())" -> pure ".ok n env"
      Just "pure Fail" -> pure ".fail"
      _ -> die ("unsupported lookahead branch: " ++ line)
