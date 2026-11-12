module Main (main) where

import Control.Monad (unless)
import Data.Char (chr, digitToInt, isHexDigit, ord)
import Data.Function (on)
import Data.List (groupBy, intercalate, isInfixOf, stripPrefix)
import qualified Data.Text as T
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

main :: IO ()
main = do
  [file] <- getArgs
  source <- lines <$> readFile file
  let argument = ["stringArg :: Text -> Loc -> Located Text -> Either Diagnostic (Located Text, Located Text)",
                  "stringArg directive l (Located al a) =",
                  "  case (isValidIdent name, T.uncons quoted) of",
                  "    (True, Just ('\"', body)) -> do",
                  "      (decoded, after) <- decodeString strLoc (T.unpack body)",
                  "      if not (T.null (T.strip (T.pack after)))",
                  "        then Left formError",
                  "        else check decoded",
                  "    _ -> Left formError",
                  "  where",
                  "    (name, rest) = T.break isSpace a",
                  "    gap = T.takeWhile isSpace rest",
                  "    quoted = T.drop (T.length gap) rest",
                  "    strLoc = advanceLoc al (name <> gap)",
                  "    formError = Diagnostic l (\"%\" <> directive <> (if directive == \"expect\" then \" expects a rule name and a string\" else \" expects a label and a string\"))",
                  "    what = if directive == \"expect\" then \"the description\" else \"the message\"",
                  "    check v",
                  "      | T.null v = Left (Diagnostic strLoc (what <> \" is empty\"))",
                  "      | T.any (\\c -> c < ' ' || c == '\\DEL') v = Left (Diagnostic strLoc (what <> \" contains a control character\"))",
                  "      | otherwise = Right (Located al name, Located strLoc v)"]
  unless (argument `isInfixOf` source) (die "unsupported string argument definition")
  let collect = ["    stringArgs d = [(l, stringArg d l (Located al a)) | TDirective l d' al a <- items, d' == d, not (T.null a)]",
                 "    expects = stringArgs \"expect\"", "    messages = stringArgs \"message\""]
  unless (collect `isInfixOf` source) (die "unsupported stringArgs collection")
  let entry = ["decodeString :: Loc -> String -> Either Diagnostic (Text, String)",
               "decodeString start = go (next start '\"') []",
               "  where", "    next l c = advanceLoc l (T.singleton c)"]
  unless (entry `isInfixOf` source) (die "unsupported decoder entry")
  let plain = ["    go l acc = \\case",
               "      [] -> Left (Diagnostic l \"unterminated literal\")",
               "      '\"' : rest -> Right (T.pack (reverse acc), rest)",
               "      '\\\\' : rest -> escape l (next l '\\\\') acc rest",
               "      c : rest -> go (next l c) (c : acc) rest"]
  unless (plain `isInfixOf` source) (die "unsupported literal decoder branch")
  let branch = [ "    escape back l acc = \\case"
               , "      [] -> Left (Diagnostic l \"unterminated literal\")"
               , "      'u' : rest -> unicode back (next l 'u') acc rest"
               , "      c : rest -> case lookup c simple of"
               , "        Just d -> go (next l c) (d : acc) rest"
               , "        Nothing -> Left (Diagnostic l (\"unknown escape \\\\\" <> T.singleton c))" ]
  unless (branch `isInfixOf` source) (die "unsupported escape branch")
  let unicode = ["    unicode back l acc = \\case",
                 "      '{' : rest ->",
                 "        let (h, rest') = span isHexDigit rest",
                 "            l' = advanceLoc (next l '{') (T.pack h)",
                 "            n = foldl (\\m d -> m * 16 + toInteger (digitToInt d)) 0 h",
                 "         in case rest' of",
                 "              '}' : more",
                 "                | not (null h) && n <= 0x10FFFF -> go (next l' '}') (chr (fromInteger n) : acc) more",
                 "                | otherwise -> Left (Diagnostic back \"invalid \\\\u escape\")",
                 "              _ -> Left (Diagnostic l' \"expected '}'\")",
                 "      _ -> Left (Diagnostic l \"expected '{'\")"]
  unless (unicode `isInfixOf` source) (die "unsupported unicode branch")
  case [entries | line <- source, Just raw <- [stripPrefix "    simple = " line],
                  Just entries <- [readMaybe raw :: Maybe [(Char, Char)]]] of
    [entries] -> do
      putStrLn "import AssembleValidation"
      putStrLn "namespace PegHs.TranslatedEscapes"
      let digits = [(ord c, ord c - digitToInt c) | c <- [minBound .. maxBound], isHexDigit c]
          groups = groupBy ((==) `on` snd) digits
      -- Observe Text.pack's treatment of every value that the unicode branch
      -- can pass to chr. Only surrogates may change during packing.
      let packed n = T.unpack (T.pack [chr n])
          scalar n = if 0xD800 <= n && n <= 0xDFFF then 0xFFFD else n
          maximumCode = ord (maxBound :: Char)
      unless (all (\n -> packed n == [chr (scalar n)]) [0 .. maximumCode])
        (die "unsupported Text.pack scalar mapping")
      putStrLn ("def maximumCode : Nat := " ++ show maximumCode)
      putStrLn "def packedChr (n : Nat) : Char :="
      putStrLn "  Char.ofNat (if 0xD800 ≤ n && n ≤ 0xDFFF then 0xFFFD else n)"
      putStrLn "def hexDigit (c : Char) : Option Nat :="
      mapM_ emitRange groups
      putStrLn "  none"
      putStrLn "def table : List (Char × Char) :="
      putStrLn ("  [" ++ intercalate ", " (map pair entries) ++ "]")
      putStrLn "def escape (go unicode : List Char → List Char → Except String α)"
      putStrLn "    (acc : List Char) : List Char → Except String α"
      putStrLn "  | [] => .error \"unterminated literal\""
      putStrLn "  | 'u' :: rest => unicode acc rest"
      putStrLn "  | c :: rest => match table.lookup c with"
      putStrLn "    | some d => go (d :: acc) rest"
      putStrLn "    | none => .error (\"unknown escape \\\\\" ++ String.singleton c)"
      putStrLn "def plain (go escaped : List Char → List Char → Except String (List Char × List Char))"
      putStrLn "    (acc : List Char) : List Char → Except String (List Char × List Char)"
      putStrLn "  | [] => .error \"unterminated literal\""
      putStrLn "  | '\"' :: rest => .ok (acc.reverse, rest)"
      putStrLn "  | '\\\\' :: rest => escaped acc rest"
      putStrLn "  | c :: rest => go (c :: acc) rest"
      putStrLn "def unicode (go : List Char → List Char → Except String α) (acc : List Char) :"
      putStrLn "    List Char → Except String α"
      putStrLn "  | '{' :: rest =>"
      putStrLn "    let h := rest.takeWhile (fun c => (hexDigit c).isSome)"
      putStrLn "    let n := h.foldl (fun m d => m * 16 + (hexDigit d).getD 0) 0"
      putStrLn "    match rest.dropWhile (fun c => (hexDigit c).isSome) with"
      putStrLn "    | '}' :: more => if !h.isEmpty && n ≤ 0x10FFFF then go (packedChr n :: acc) more"
      putStrLn "      else .error \"invalid \\\\u escape\""
      putStrLn "    | _ => .error \"expected '}'\""
      putStrLn "  | _ => .error \"expected '{'\""
      putStrLn "def argument (valid : String → Bool) (decode : List Char → Except String (List Char × List Char))"
      putStrLn "    (directive arg : String) : Except String (String × List Char) := do"
      putStrLn "  let name := arg.toList.takeWhile (fun c => !PegVerification.ghcIsSpace c)"
      putStrLn "  let rest := arg.toList.dropWhile (fun c => !PegVerification.ghcIsSpace c)"
      putStrLn "  let quoted := rest.drop (rest.takeWhile PegVerification.ghcIsSpace).length"
      putStrLn "  let form := PegHs.AssembleValidationHelpers.formError directive"
      putStrLn "  let what := if directive == \"expect\" then \"the description\" else \"the message\""
      putStrLn "  match valid (String.ofList name), quoted with"
      putStrLn "  | true, '\"' :: body =>"
      putStrLn "    let (v, tail) ← decode body"
      putStrLn "    if !(PegHs.AssembleValidationHelpers.stripSpace tail).isEmpty then .error form"
      putStrLn "    else if v.isEmpty then .error (what ++ \" is empty\")"
      putStrLn "    else if v.any (fun c => c.toNat < 32 || c.toNat == 127) then .error (what ++ \" contains a control character\")"
      putStrLn "    else .ok (String.ofList name, v)"
      putStrLn "  | _, _ => .error form"
      putStrLn "def collect (parse : String → String → β) (directive : String)"
      putStrLn "    (items : List (α × PegHs.AssembleValidation.Top)) : List (α × β) :="
      putStrLn "  items.filterMap fun (loc, top) => match top with"
      putStrLn "    | .directive d a => if d == directive && !a.isEmpty then some (loc, parse directive a) else none"
      putStrLn "    | _ => none"
      putStrLn "end PegHs.TranslatedEscapes"
    _ -> die "unsupported simple escape table"
  where
    emitRange [] = die "empty hexadecimal range"
    emitRange xs@((lo, offset):_) = do
      let hi = fst (last xs)
      unless (map fst xs == [lo .. hi]) (die "non-contiguous hexadecimal range")
      putStrLn ("  if " ++ show lo ++ " ≤ c.toNat && c.toNat ≤ " ++ show hi
        ++ " then some (c.toNat - " ++ show offset ++ ") else")
    pair (a,b) = "(Char.ofNat " ++ show (ord a) ++ ", Char.ofNat " ++ show (ord b) ++ ")"
