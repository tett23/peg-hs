-- | @peg-hs label@: insert the labels that the label check shows to be
-- safe (ADR 0054).
--
-- A label is named @Rule_target@, after its rule and its expression: the
-- rule of a reference, the text of a literal of identifier characters,
-- @lit@ for other literals, @class@, @any@, @group@, and for a literal of
-- one symbol a name of this table ('Peg.Grammar.LabelInsertion.symbolNames'):
--
-- @
-- (  lparen     )  rparen     [  lbracket   ]  rbracket   {  lbrace     }  rbrace
-- <  lt         >  gt         ,  comma      ;  semi       :  colon      .  dot
-- =  eq         +  plus       -  minus      *  star       /  slash      \\  backslash
-- |  bar        &  amp        !  bang       ?  question   #  hash       %  percent
-- ^  caret      ~  tilde      \@  at         $  dollar     `  backquote  \"  dquote
-- '  quote
-- @
module Command.Label (labelCommand) where

import qualified Data.Text as T
import Diagnostics (reportErrors)
import FileIO (readUtf8, reportFileError, writeUtf8)
import Options
import Peg.Grammar (Loc (..))
import Peg.Grammar.LabelInsertion (Insertion (..), insertLabels, symbolNames)
import System.Exit (ExitCode (..))

labelCommand :: Command
labelCommand =
  Command
    { cmdName = "label"
    , cmdSummary = "insert the labels that are shown to be safe"
    , cmdArguments = "GRAMMAR.hpeg"
    , cmdDescription =
        [ "Find the positions where a label would be safe, and list the labels as FILE:LINE:COLUMN: ^NAME"
        , "at the start of their expressions. A position is an item of a sequence after an item that"
        , "always consumes input, and is kept only if the label check of peg-hs gen shows that the"
        , "label cannot reject valid input. The labels therefore do not change the language. Nothing is"
        , "inserted inside a label that has a recovery rule (%recover) or in the rules it calls, and no"
        , "%recover or %safe is written. The file is read and written as UTF-8."
        , ""
        , "A label is named RULE_TARGET after its rule and its expression: the rule of a reference, the"
        , "text of a literal of identifier characters, lit for other literals, class, any and group, and"
        , "for a literal of one symbol:"
        ]
          ++ symbolTable
          ++ ["A name already used gets _2, _3 and so on."]
    , cmdOptions =
        [ Opt "write" Nothing Nothing "insert the labels in the file, and list them"
        , Opt "rule" Nothing (Just "RULE") "insert only in RULE; can be given more than once"
        ]
    , cmdExamples =
        [ ("peg-hs label Expr.hpeg", "list the labels that can be inserted in Expr.hpeg")
        , ("peg-hs label --write --rule Stmt Lua.hpeg", "insert the labels in the rule Stmt of Lua.hpeg")
        ]
    , cmdRun = run
    }

-- The names of the symbols, six to a line.
symbolTable :: [String]
symbolTable = go symbolNames
  where
    go [] = [""]
    go xs = T.unpack (T.stripEnd (T.pack ("  " <> concatMap cell (take 6 xs)))) : go (drop 6 xs)
    cell (c, n) = let s = [c] <> " " <> T.unpack n in s <> replicate (13 - length s) ' '

run :: Parsed -> IO ExitCode
run p = case parsedArguments p of
  [input] ->
    readUtf8 "peg-hs label takes a grammar file, not a directory" input >>= \case
      Left e -> reportFileError e >> pure (ExitFailure 1)
      Right src -> case insertLabels [T.pack r | ("rule", r) <- parsedOptions p] src of
        Left diags -> reportErrors input diags >> pure (ExitFailure 1)
        Right (labels, out) -> do
          written <-
            if flag "write" p && out /= src
              then writeUtf8 input out
              else pure (Right ())
          case written of
            Left e -> reportFileError e >> pure (ExitFailure 1)
            Right () -> do
              mapM_ (putStrLn . line input) labels
              pure ExitSuccess
  [] -> commandUsageError "label" "label needs a grammar file"
  _ -> commandUsageError "label" "label takes one grammar file"

line :: FilePath -> Insertion -> String
line file i =
  let Loc l c = insertionStart i
   in file <> ":" <> show l <> ":" <> show c <> ": ^" <> T.unpack (insertionName i)
