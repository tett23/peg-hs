-- | @peg-hs lsp@: the language server (ADR 0035).
module Command.Lsp (lspCommand) where

import Options
import Peg.Lsp (runServer)
import System.Exit (ExitCode (..))
import System.IO (stdin, stdout)

lspCommand :: Command
lspCommand =
  Command
    { cmdName = "lsp"
    , cmdSummary = "run the language server on standard input and output"
    , cmdArguments = ""
    , cmdDescription =
        [ "Run the language server of the .hpeg notation, speaking the language server protocol"
        , "on standard input and output: diagnostics, formatting, semantic tokens, definitions,"
        , "references, hover and document symbols."
        ]
    , cmdOptions = []
    , cmdExamples =
        [ ("peg-hs lsp", "run by an editor; the README has the settings of VS Code, Neovim and Helix")
        ]
    , cmdRun = run
    }

run :: Parsed -> IO ExitCode
run p = case parsedArguments p of
  [] -> runServer stdin stdout >>= \code -> pure (if code == 0 then ExitSuccess else ExitFailure code)
  _ -> commandUsageError "lsp" "lsp takes no arguments"
