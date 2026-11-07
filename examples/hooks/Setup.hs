-- cabal builds a setup script of its own for build-type: Hooks. This file
-- is for cabal check, which wants one.
module Main (main) where

import Distribution.Simple (defaultMainWithSetupHooks)
import SetupHooks (setupHooks)

main :: IO ()
main = defaultMainWithSetupHooks setupHooks
