{-# LANGUAGE OverloadedStrings #-}
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Peg.Grammar.SelfHosted as P
import qualified Peg.Grammar.SelfHostedSyntax as S
import Peg.Runtime.Internal

inputs :: [T.Text]
inputs = ["", " ", "#comment\n", "%module M\nS :: ()\nS <- 'a'\n",
  "%module M\nS :: ()\nS <- [a-z]+\n", "%module M\nS :: ()\nS <- (\n",
  "%module M\nS :: ()\nS <- 'a' { let }\n", "%module M\nS :: ()\nS <- & 'a' 'a'\n"]

main :: IO ()
main = mapM_ check (zip [0 :: Int ..] inputs)
  where
    check (i, input) = do
      let fast = defaultConfig {cfgCount = True}
          slow = fast {cfgMemo = False}
          (pr, ps) = P.peg'parseWith fast input
          (qr, qs) = P.peg'parseWith slow input
          (sr, ss) = S.peg'parseWith fast input
          (tr, ts) = S.peg'parseWith slow input
          counts st = M.elems (statsEvaluations st)
      if pr /= qr || sr /= tr ||
         any (> 1) (counts ps) || any (> 1) (counts ss)
        then error ("memo mismatch: case " ++ show i)
        else putStrLn ("case " ++ show i ++ " ok, memo evals " ++
          show (sum (counts ps), sum (counts ss)) ++
          ", no-memo evals " ++ show (sum (counts qs), sum (counts ts)))
