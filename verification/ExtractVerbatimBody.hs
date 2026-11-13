module Main (main) where

import Data.List (stripPrefix)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  [path] <- getArgs
  source <- lines <$> readFile path
  let body = takeWhile (not . null) (dropWhile (/= "verbatimBody l body =") source)
  let advance = takeWhile (not . null) (dropWhile (/= "advanceLoc = T.foldl' step") source)
  let param = takeWhile (not . null) (dropWhile (/= "toParam (Located l t) = case T.breakOn \"::\" t of") source)
  if param ==
      [ "toParam (Located l t) = case T.breakOn \"::\" t of"
      , "  (n, rest)"
      , "    | not (T.null rest)"
      , "    , let name = T.strip n"
      , "    , isValidIdent name ->"
      , "        let afterSep = T.drop 2 rest"
      , "            lead = T.takeWhile isSpace afterSep"
      , "            tyLoc = advanceLoc l (n <> \"::\" <> lead)"
      , "            ty = T.strip afterSep"
      , "         in if T.null ty then Left \"expected a parameter type\" else Right (Param name (Located tyLoc ty))"
      , "  _ -> Left \"expected a parameter of the form name :: Type\"" ]
    then pure () else die "unsupported toParam"
  case advance of
    ["advanceLoc = T.foldl' step", "  where",
     "    step (Loc f l _) '\\n' = Loc f (l + 1) 1",
     "    step (Loc f l c) _ = Loc f l (c + 1)"] -> pure ()
    _ -> die "unsupported advanceLoc"
  case body of
    ["verbatimBody l body =", "  let (start, text) = case T.uncons body of",
     "        Just ('\\n', rest) -> (Loc (locFile l) (locLine l + 1) 1, rest)",
     "        _ -> (l, T.stripStart body)", finish]
      | Just "T.stripEnd text)" <- stripPrefix "   in (start, " finish ->
          putStrLn $ unlines
            [ "import ParameterPredicates", "import Whitespace", "namespace PegHs.MetaExecution"
            , "def translatedAdvanceLoc (loc : α × Nat × Nat) (text : List Char) := text.foldl (fun (f,l,c) ch => if ch = '\\n' then (f,l+1,1) else (f,l,c+1)) loc"
            , "def translatedVerbatimBody (file : α) (line column : Nat) (body : List Char) : (α × Nat × Nat) × List Char :="
            , "  let (loc, text) := match body with"
            , "    | '\\n' :: rest => ((file, line + 1, 1), rest)"
            , "    | _ => ((file, line, column), body.dropWhile PegVerification.ghcIsSpace)"
            , "  (loc, ParameterPredicates.stripEnd PegVerification.ghcIsSpace text)"
            , "def translatedToParam (space alpha alnum : Char → Bool) (loc : α × Nat × Nat) (src : List Char) : Except String (List Char × (α × Nat × Nat) × List Char) :="
            , "  match ParameterPredicates.splitParam src with"
            , "  | some (n, rest) =>"
            , "    let name := ParameterPredicates.strip space n"
            , "    if ParameterPredicates.identifier alpha alnum name then"
            , "      let ty := ParameterPredicates.strip space rest"
            , "      if ty.isEmpty then .error \"expected a parameter type\""
            , "      else .ok (name, translatedAdvanceLoc loc (n ++ [':', ':'] ++ rest.takeWhile space), ty)"
            , "    else .error \"expected a parameter of the form name :: Type\""
            , "  | none => .error \"expected a parameter of the form name :: Type\""
            , "end PegHs.MetaExecution" ]
    _ -> die "unsupported verbatimBody"
