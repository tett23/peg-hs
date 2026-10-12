-- | @peg-hs@: the command line tool of peg-hs (ADR 0037).
module Main (main) where

import Command.Fmt (fmtCommand)
import Command.Gen (genCommand)
import Command.Lint (lintCommand)
import Command.Lsp (lspCommand)
import Command.Parse (parseCommand)
import Data.List (find, isSuffixOf)
import Data.Version (showVersion)
import Options
import Paths_peg_cli (version)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.IO (hPutStr, stderr)

commands :: [Command]
commands = [genCommand, fmtCommand, lintCommand, lspCommand, parseCommand]

overview :: String
overview =
  unlines $
    ["usage: peg-hs <command> [options] [arguments]", "", "commands:"]
      ++ ["  " <> cmdName c <> replicate (8 - length (cmdName c)) ' ' <> cmdSummary c | c <- commands]
      ++ ["  help    show the commands, or the help of a command", "", "Run peg-hs help <command> for the options of a command."]

main :: IO ()
main = getArgs >>= dispatch >>= exitWith

dispatch :: [String] -> IO ExitCode
dispatch = \case
  [] -> hPutStr stderr overview >> pure (ExitFailure 2)
  ["--version"] -> putStrLn ("peg-hs " <> showVersion version) >> pure ExitSuccess
  [a] | a `elem` ["-h", "--help", "help"] -> putStr overview >> pure ExitSuccess
  ["help", name] -> case lookupCommand name of
    Just c -> putStr (commandHelp c) >> pure ExitSuccess
    Nothing -> unknown name
  "help" : _ -> usageError "help takes at most one command"
  name : rest -> case lookupCommand name of
    Just c
      | any (`elem` ["-h", "--help"]) rest -> putStr (commandHelp c) >> pure ExitSuccess
      | otherwise -> either usageError (cmdRun c) (parseOptions (cmdOptions c) rest)
    Nothing
      | ".peg" `isSuffixOf` name -> usageError ("no command: to generate a module, use peg-hs gen " <> name)
      | otherwise -> unknown name
  where
    lookupCommand name = find ((== name) . cmdName) commands
    unknown name = hPutStr stderr overview >> usageError ("unknown command " <> name)
