{-# LANGUAGE StaticPointers #-}

-- | The hooks of the example: the parser of grammar/Calc.hpeg from
-- peg-hooks, and a rule of the package itself that writes the module
-- Calc.Greeting. The two are joined with '<>'.
module SetupHooks (setupHooks) where

import Data.List.NonEmpty (NonEmpty (..))
import Distribution.Simple.LocalBuildInfo (interpretSymbolicPathLBI)
import Distribution.Simple.SetupHooks
import Distribution.Utils.Path (makeRelativePathEx)
import Distribution.Utils.ShortText (toShortText)
import Peg.Hooks (Grammar (..), pegSetupHooks)
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeDirectory)

setupHooks :: SetupHooks
setupHooks = pegSetupHooks [Grammar "grammar/Calc.hpeg" "Calc.Parser"] <> greetingHooks

greetingHooks :: SetupHooks
greetingHooks =
  noSetupHooks
    { buildHooks = noBuildHooks {preBuildComponentRules = Just (rules (static ()) greetingRules)}
    }

greetingRules :: PreBuildComponentInputs -> RulesM ()
greetingRules (PreBuildComponentInputs _ lbi tgt) = do
  let out = Location (autogenComponentModulesDir lbi (targetCLBI tgt)) (makeRelativePathEx "Calc/Greeting.hs")
  registerRule_ (toShortText "calc:greeting") $
    staticRule (mkCommand (static Dict) (static writeGreeting) (interpretSymbolicPathLBI lbi (location out))) [] (out :| [])

writeGreeting :: FilePath -> IO ()
writeGreeting path = do
  createDirectoryIfMissing True (takeDirectory path)
  writeFile path $
    unlines
      [ "module Calc.Greeting (greeting) where"
      , ""
      , "greeting :: String"
      , "greeting = \"calc: an expression on a line\""
      ]
