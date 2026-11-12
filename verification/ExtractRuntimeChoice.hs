-- Translate the result projection of choice with recovery disabled.
module Main (main) where

import Data.List (isPrefixOf)
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
          putStrLn "    | other => other\nend PegHs.EnvironmentEval"
    _ -> die "unsupported runtime choice"
