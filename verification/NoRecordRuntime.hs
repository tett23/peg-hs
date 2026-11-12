{-# LANGUAGE OverloadedStrings #-}
import Control.Monad (unless)
import qualified Data.Map.Strict as M
import qualified Fixture.Indent as Indent
import Peg.Runtime.Internal (Config (..), Stats (..), defaultConfig)

main :: IO ()
main = do
  let tabbed = "a\n\tb\n"
      expected = Right [Indent.Node "a" [Indent.Node "b" []]]
      cfg = defaultConfig {cfgCount = True, cfgMemo = False}
  unless (Indent.parse tabbed == expected) $ fail "ordinary tabstop parse changed"
  unless (fst (Indent.peg'parseWith cfg tabbed) == expected) $
    fail "debug Config lost the grammar tabstop"
  let (result, stats) = Indent.peg'parseWith cfg "a\n  b\nc\n"
  unless (result == Right [Indent.Node "a" [Indent.Node "b" []], Indent.Node "c" []]) $
    fail "debug Config changed parsing"
  unless (M.lookup ("Node", 6) (statsEvaluations stats) == Just 3) $
    fail "debug Config lost counting"
