-- | @peg-hs@: the command line tool of peg-hs (ADR 0037).
module Main (main) where

import Command.Fmt (fmtCommand)
import Command.Gen (genCommand)
import Command.Lint (lintCommand)
import Command.Lsp (lspCommand)
import Command.Parse (parseCommand)
import Data.List (find, intercalate, isSuffixOf)
import Data.Version (showVersion)
import EditDistance (suggestions)
import FileIO (setUtf8StdHandles)
import Options
import Paths_peg_cli (version)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.IO (hPutStr, hPutStrLn, stderr)

commands :: [Command]
commands = [genCommand, fmtCommand, lintCommand, lspCommand, parseCommand]

overview :: String
overview =
  unlines $
    ["usage: peg-hs <command> [options] [arguments]", "", "commands:"]
      ++ ["  " <> cmdName c <> replicate (8 - length (cmdName c)) ' ' <> cmdSummary c | c <- commands]
      ++ [ "  help    show the commands, or the help of a command"
         , ""
         , "options:"
         , "  -h, --help    show this help"
         , "  --version     show the version of peg-hs"
         , ""
         , "Run peg-hs help <command> for the options and examples of a command. An option that"
         , "takes a value takes it as --name VALUE or as --name=VALUE."
         ]

main :: IO ()
main = setUtf8StdHandles >> getArgs >>= dispatch >>= exitWith

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
      | otherwise -> either (commandUsageError (cmdName c)) (cmdRun c) (parseOptions (cmdOptions c) rest)
    Nothing
      | ".peg" `isSuffixOf` name -> usageError ("no command: to generate a module, use peg-hs gen " <> name)
      | otherwise -> unknown name
  where
    lookupCommand name = find ((== name) . cmdName) commands
    unknown name = do
      hPutStrLn stderr ("peg-hs: unknown command " <> name)
      case suggestions ("help" : map cmdName commands) name of
        [] -> pure ()
        cs -> hPutStrLn stderr ("Did you mean " <> intercalate " or " cs <> "?")
      hPutStrLn stderr "Run peg-hs help for the commands."
      pure (ExitFailure 2)
