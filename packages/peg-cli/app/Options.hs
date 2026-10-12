-- | Commands and their options (ADR 0037). Options are parsed by hand from
-- a table per command, which also makes the help text.
module Options
  ( Command (..)
  , Opt (..)
  , Parsed (..)
  , flag
  , value
  , parseOptions
  , commandHelp
  , usageError
  ) where

import Data.List (find, isPrefixOf)
import System.Exit (ExitCode (..))
import System.IO (hPutStrLn, stderr)

-- | A command of peg-hs.
data Command = Command
  { cmdName :: String
  , cmdSummary :: String
  -- ^ One line for the list of commands.
  , cmdArguments :: String
  -- ^ The arguments in the usage line, such as @GRAMMAR.peg@.
  , cmdDescription :: [String]
  , cmdOptions :: [Opt]
  , cmdRun :: Parsed -> IO ExitCode
  }

-- | An option: its long name, short name, the name of its value if it takes
-- one, and its help.
data Opt = Opt
  { optLong :: String
  , optShort :: Maybe Char
  , optValue :: Maybe String
  , optHelp :: String
  }

-- | The options and arguments given to a command.
data Parsed = Parsed
  { parsedOptions :: [(String, String)]
  , parsedArguments :: [String]
  }

-- | Whether an option without a value was given.
flag :: String -> Parsed -> Bool
flag name p = any ((== name) . fst) (parsedOptions p)

-- | The value of an option, the last one if given more than once.
value :: String -> Parsed -> Maybe String
value name p = case [v | (n, v) <- parsedOptions p, n == name] of
  [] -> Nothing
  vs -> Just (last vs)

-- | Parse the arguments of a command.
parseOptions :: [Opt] -> [String] -> Either String Parsed
parseOptions opts = go [] []
  where
    go os as [] = Right (Parsed (reverse os) (reverse as))
    go os as (a : rest)
      | "-" `isPrefixOf` a && a /= "-" = case find (matches a) opts of
          Nothing -> Left ("unknown option " <> a)
          Just o -> case (optValue o, rest) of
            (Nothing, _) -> go ((optLong o, "") : os) as rest
            (Just _, v : rest') -> go ((optLong o, v) : os) as rest'
            (Just _, []) -> Left ("the option " <> a <> " needs a value")
      | otherwise = go os (a : as) rest
    matches a o = a == "--" <> optLong o || maybe False (\c -> a == ['-', c]) (optShort o)

-- | The help of a command.
commandHelp :: Command -> String
commandHelp c =
  unlines $
    ["usage: peg-hs " <> cmdName c <> (if null (cmdArguments c) then "" else " " <> cmdArguments c) <> (if null (cmdOptions c) then "" else " [options]"), ""]
      ++ cmdDescription c
      ++ (if null (cmdOptions c) then [] else ["", "options:"] ++ map line (cmdOptions c))
  where
    line o =
      let names = maybe "" (\s -> ['-', s] <> ", ") (optShort o) <> "--" <> optLong o <> maybe "" (" " <>) (optValue o)
       in "  " <> names <> replicate (max 1 (26 - length names)) ' ' <> optHelp o

-- | Report a mistake in the use of a command, with exit status 2.
usageError :: String -> IO ExitCode
usageError msg = do
  hPutStrLn stderr ("peg-hs: " <> msg)
  pure (ExitFailure 2)
