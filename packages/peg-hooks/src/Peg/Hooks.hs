{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StaticPointers #-}

-- | Setup hooks that generate the modules of @.hpeg@ grammars in the build
-- of a cabal package (ADR 0085).
--
-- A package with @build-type: Hooks@ makes 'pegSetupHooks' the
-- @setupHooks@ of its @SetupHooks.hs@:
--
-- @
-- module SetupHooks (setupHooks) where
--
-- import Distribution.Simple.SetupHooks (SetupHooks)
-- import Peg.Hooks (Grammar (..), pegSetupHooks)
--
-- setupHooks :: SetupHooks
-- setupHooks = pegSetupHooks [Grammar \"grammar\/Calc.hpeg\" \"Calc.Parser\"]
-- @
--
-- Its @.cabal@ file has @cabal-version: 3.14@ or later, names @peg-hooks@
-- and @Cabal-hooks@ in the @setup-depends@ of its @custom-setup@ stanza,
-- and lists each module in @autogen-modules@ as well as in
-- @other-modules@ or @exposed-modules@. Each grammar goes in
-- @extra-source-files@: cabal does not see a change of a file that is not
-- listed, and keeps the old module.
--
-- Before each component of the package is built, a rule of the hooks reads
-- each grammar, checks it as @peg-hs gen@ does and writes its module to the
-- autogen directory of the component. The rule runs again when the grammar
-- changes. Errors stop the build and are written to standard error as
-- @grammar\/Calc.hpeg:3:5: error: ...@; the warnings about labels are
-- written as @grammar\/Calc.hpeg:3:5: warning: ...@ and do not stop it. The
-- @LINE@ pragmas of the module name the grammar by the path given in
-- 'Grammar', so GHC reports type errors of actions at the lines of the
-- grammar.
module Peg.Hooks
  ( Grammar (..)
  , pegSetupHooks
  ) where

import Control.Monad (forM_, unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Distribution.ModuleName (ModuleName)
import qualified Distribution.ModuleName as ModuleName
import Distribution.Parsec (simpleParsec)
import Distribution.Simple.LocalBuildInfo (interpretSymbolicPathLBI)
import Distribution.Simple.SetupHooks
import Distribution.Simple.Utils (notice)
import Distribution.Types.Component (componentBuildInfo)
import Distribution.Utils.Path (makeRelativePathEx, sameDirectory)
import Distribution.Utils.ShortText (toShortText)
import Peg.Codegen (Generation (..), Options (..), defaultOptions, generateWithWarnings, renderWarning)
import qualified Peg.Grammar as G
import System.Directory (canonicalizePath, createDirectoryIfMissing)
import System.Exit (die, exitFailure)
import System.FilePath (isAbsolute, joinPath, splitDirectories, takeDirectory)
import System.IO (IOMode (..), hSetEncoding, stderr, utf8, withFile)

-- | A grammar of the package and the module generated from it.
data Grammar = Grammar
  { grammarPath :: FilePath
  -- ^ The path of the grammar, relative to the root of the package, such
  -- as @grammar\/Calc.hpeg@. The @LINE@ pragmas of the module and the
  -- diagnostics name the grammar by this path.
  , grammarModuleName :: String
  -- ^ The name of the generated module, such as @Calc.Parser@. It must be
  -- the name that the @%module@ of the grammar gives, or the build stops
  -- with an error at @%module@. The rule has to declare the file it writes
  -- before it reads the grammar, so the name is given here too.
  }
  deriving (Eq, Show)

-- | Hooks with a pre-build rule for each grammar. Join them to other hooks
-- of the package with '<>'.
--
-- A component gets the rule of a grammar when it lists the module of the
-- grammar in @autogen-modules@; cabal runs only the rules whose files a
-- component needs. A module not listed there is not generated, and GHC
-- reports that it cannot find it.
--
-- A grammar whose path is absolute, or whose module name is not the name
-- of a module, stops the build before anything is built.
pegSetupHooks :: [Grammar] -> SetupHooks
pegSetupHooks gs =
  noSetupHooks
    { buildHooks = noBuildHooks {preBuildComponentRules = Just (rules (static ()) (grammarRules gs))}
    }

-- What a rule passes to 'runRule': the verbosity, the path of the grammar
-- as given, the paths of the grammar and of the module to read and write,
-- the root of the package, and the name of the module.
type Job = (Verbosity, FilePath, FilePath, FilePath, FilePath, String)

grammarRules :: [Grammar] -> PreBuildComponentInputs -> RulesM ()
grammarRules gs (PreBuildComponentInputs what lbi tgt) =
  forM_ gs $ \(Grammar path name) -> do
    m <- liftIO (moduleName path name)
    when (m `elem` autogenModules (componentBuildInfo (targetComponent tgt))) $
      registerRule_ (toShortText ("peg-hooks:" <> path)) $
        staticRule (mkCommand (static Dict) (static runRule) (job path name m)) [FileDependency (input path)] (output m :| [])
  where
    input path = Location sameDirectory (makeRelativePathEx path)
    output m = Location (autogenComponentModulesDir lbi (targetCLBI tgt)) (makeRelativePathEx (ModuleName.toFilePath m <> ".hs"))
    job path name m =
      ( buildingWhatVerbosity what
      , path
      , interpretSymbolicPathLBI lbi (location (input path))
      , interpretSymbolicPathLBI lbi (location (output m))
      , interpretSymbolicPathLBI lbi sameDirectory
      , name
      ) ::
        Job

moduleName :: FilePath -> String -> IO ModuleName
moduleName path name = do
  when (isAbsolute path) $
    die ("peg-hooks: the path of a grammar is relative to the package: " <> path)
  maybe (die ("peg-hooks: not the name of a module: " <> name)) pure (simpleParsec name)

runRule :: Job -> IO ()
runRule (verbosity, path, input, output, root, name) = do
  notice verbosity ("peg-hooks: generating " <> name <> " from " <> path)
  createDirectoryIfMissing True (takeDirectory output)
  base <- canonicalizePath root
  out <- canonicalizePath output
  src <- withFile input ReadMode (\h -> hSetEncoding h utf8 >> TIO.hGetContents h)
  let opts = defaultOptions {optSourceName = path, optOutputName = relativeTo base out}
      failWith ds = mapM_ (TIO.hPutStrLn stderr . G.renderDiagnostic path) ds >> exitFailure
  gen <- either failWith pure (generateWithWarnings opts Nothing src)
  let G.Located loc declared = G.grammarModule (generationGrammar gen)
  unless (declared == T.pack name) $
    failWith [G.Diagnostic loc ("%module is " <> declared <> ", but the Grammar of peg-hooks names " <> T.pack name)]
  mapM_ (TIO.hPutStrLn stderr . renderWarning path) (generationWarnings gen)
  code <- either failWith pure (generationModule gen)
  withFile output WriteMode (\h -> hSetEncoding h utf8 >> TIO.hPutStr h code)

-- The path of a file relative to a directory, both canonical, with ".."
-- for the directories above; the file's own path when the two have no
-- root in common (two drives of Windows). The module of a grammar names
-- itself in its LINE pragmas by this path, so that the module does not
-- name the directories of the machine.
relativeTo :: FilePath -> FilePath -> FilePath
relativeTo dir file = case (splitDirectories dir, splitDirectories file) of
  (d : ds, f : fs) | d == f -> let (up, down) = dropCommon ds fs in joinPath (map (const "..") up <> down)
  _ -> file
  where
    dropCommon (x : xs) (y : ys) | x == y = dropCommon xs ys
    dropCommon xs ys = (xs, ys)
