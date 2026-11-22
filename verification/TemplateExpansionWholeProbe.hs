{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The probe of TemplateExpansionWhole.lean. With the argument @lean@ it
-- writes the parsed grammars, and the identifiers of every piece of code in
-- them, as a Lean module for the model. With @expect@ it writes what the real
-- 'expandTemplates' returns for them, in the format of
-- TemplateExpansionWholeProbe.lean. The types of the rules are not written:
-- the model leaves 'instanceType' and 'classify' abstract.
module Main (main) where

import Data.Char (ord)
import Data.List (intercalate, nub)
import Data.Maybe (isJust, maybeToList)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Numeric (showHex)
import Peg.Grammar
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import System.Environment (getArgs)
import System.Exit (die)

cases :: IO [(String, Text)]
cases = do
  fixture <- TIO.readFile "packages/peg-codegen/test/fixtures/Templates.hpeg"
  pure
    [ ("plain", T.unlines ["%module M", "S <- 'a' B", "B <- [b-c]+ { () }"])
    , ("fixture", fixture)
    , ( "parameters"
      , T.unlines
          [ "%module M"
          , "S :: ()"
          , "S <- B(0) N { () }"
          , "Lines<p> :: ()"
          , "Lines<p> <- p ('\\n' p)* { () }"
          , "Item(n :: Int) :: ()"
          , "Item <- &{ n >= 0 } 'i' { () }"
          , "Indented<p>(n :: Int) :: ()"
          , "Indented<p> <- &{ n >= 0 } p { () }"
          , "B(ind :: Int, k :: Int) :: ()"
          , "B <- Lines<Item(ind)> Indented<Item(ind)>(ind + 2) Indented<Item(0)>(1) x:N (y:N Lines<Item(k)>) Lines<Item(k)> Ignore<Item(k)> { () }"
          , "Ignore<p> :: ()"
          , "Ignore<p> <- 'z' { () }"
          , "N :: Int"
          , "N <- d:$[0-9]+ { read (T.unpack d) }"
          ]
      )
    , ( "syntax"
      , T.unlines
          [ "%module M"
          , "%syntax"
          , "S <- List<A, ','> List<A, ','> List<B, ';'>"
          , "List<p, sep> :: ()"
          , "List<p, sep> <- p (sep p)*"
          , "A <- $'a' @CapturedA"
          , "B <- $'b' @CapturedB"
          ]
      )
    , ( "names"
      , T.unlines
          [ "%module M"
          , "S <- K<'a'> K<'b'> K'1"
          , "K'0 <- 'x'"
          , "K'1 <- 'y'"
          , "K<w> :: ()"
          , "K<w> <- w ![a-z]"
          , "R<x> :: ()"
          , "R<x> <- x R<x> / x"
          , "T <- R<'r'>"
          ]
      )
    , ( "directives"
      , T.unlines
          [ "%module M"
          , "%start List"
          , "%inline K"
          , "S <- List<A, ','>"
          , "List<p, p> :: ()"
          , "List<p, p> <- p"
          , "K<w> :: ()"
          , "K<w> <- w"
          , "A <- 'a'"
          ]
      )
    , ( "calls"
      , T.unlines
          [ "%module M"
          , "S :: ()"
          , "S <- List A<'a'> List<A> K<'a'>(1) Indented<A>(1, 2) Typed<'c'> { () }"
          , "List<p, sep> :: ()"
          , "List<p, sep> <- p (sep p)*"
          , "K<w> :: ()"
          , "K<w> <- w"
          , "Indented<p>(n :: Int) :: ()"
          , "Indented<p> <- &{ n >= 0 } p { () }"
          , "Typed<p :: a> :: a"
          , "Typed<p> <- x:p { x }"
          , "A <- 'a'"
          ]
      )
    , ( "captures"
      , T.unlines
          [ "%module M"
          , "B(ind :: Int, n :: Int) :: ()"
          , "B <- x:N Lines<Item(x)> Uses<Item(n)> { () }"
          , "Lines<p> :: ()"
          , "Lines<p> <- p ('\\n' p)* { () }"
          , "Uses<p> :: ()"
          , "Uses<p> <- p &{ n > 0 } { () }"
          , "Item(n :: Int) :: ()"
          , "Item <- 'i' { () }"
          , "N :: Int"
          , "N <- d:$[0-9]+ { read (T.unpack d) }"
          ]
      )
    , ( "scope"
      , T.unlines
          [ "%module M"
          , "S(k :: Int) :: ()"
          , "S <- (y:N Lines<Item(y)>) Lines<Item(y)> { () }"
          , "Lines<p> :: ()"
          , "Lines<p> <- p ('\\n' p)* { () }"
          , "Item(n :: Int) :: ()"
          , "Item <- 'i' { () }"
          , "N :: Int"
          , "N <- d:$[0-9]+ { read (T.unpack d) }"
          ]
      )
    , ( "body"
      , T.unlines
          [ "%module M"
          , "S <- W<'a'>"
          , "W<x> :: ()"
          , "W<x> <- x Missing<x> Other<x>"
          , "Other <- 'o'"
          ]
      )
    , ( "growth"
      , T.unlines
          [ "%module M"
          , "S <- G<'a'>"
          , "G<x> :: ()"
          , "G<x> <- x / G<(x x)>"
          ]
      )
    ]

main :: IO ()
main = do
  args <- getArgs
  cs <- cases
  parsed <- mapM (\(n, src) -> either (\ds -> die (n ++ ": " ++ show ds)) (pure . (,) n) (parseGrammar src)) cs
  case args of
    ["lean"] -> putStr (leanModule parsed)
    ["expect"] -> mapM_ (\(n, g) -> putStr (project n (expandTemplates g))) parsed
    _ -> die "usage: TemplateExpansionWholeProbe (lean|expect)"

-- The model's location of a Loc in the one file parsed.
loc :: Loc -> Int
loc (Loc _ l c) = l * 100000 + c

-- The projection, written the same way by TemplateExpansionWholeProbe.lean.
project :: String -> Either [Diagnostic] Grammar -> String
project n res =
  unlines $
    ("case " ++ n)
      : case res of
        Left ds -> "error" : ["  " ++ show (loc l) ++ " " ++ T.unpack m | Diagnostic l m <- ds]
        Right g ->
          "ok"
            : concatMap rule (grammarRules g)
              ++ ["inline " ++ show (loc l) ++ " " ++ T.unpack x | Located l x <- grammarInline g]
  where
    rule r =
      ( "rule " ++ T.unpack (ruleName r) ++ " @" ++ show (loc (ruleLoc r)) ++ " params="
          ++ intercalate "," [T.unpack (paramName p) ++ ":" ++ T.unpack (unLoc (paramType p)) | p <- ruleParams r]
          ++ " tparams=" ++ intercalate "," [T.unpack (templateParamName p) ++ maybe "" (\t -> "::" ++ T.unpack t) (templateParamType p) | p <- ruleTemplateParams r]
          ++ " annotation=" ++ maybe "-" (show . loc) (ruleAnnotation r)
      )
        : concatMap alt (ruleAlts r)
    alt a = ("  alt " ++ maybe "-" (\t -> "{" ++ T.unpack (unLoc t) ++ "}") (altAction a)
      ++ " constructor=" ++ maybe "-" (T.unpack . unLoc) (altConstructor a)) : ["    " ++ item i | i <- altItems a]
    item i = maybe "" (\b -> T.unpack b ++ ":") (itemBind i) ++ expr (itemExpr i)
    expr = \case
      ELit _ w -> "(lit " ++ T.unpack w ++ ")"
      EClass _ w -> "(class " ++ T.unpack w ++ ")"
      EAny -> "any"
      ERef l x as -> "(ref@" ++ show (loc l) ++ " " ++ T.unpack x ++ " [" ++ intercalate "," (map (T.unpack . unLoc) as) ++ "])"
      EGroup alts -> "(group " ++ intercalate " / " (map (unwords . map item) alts) ++ ")"
      EStar x -> "(star " ++ expr x ++ ")"
      EPlus x -> "(plus " ++ expr x ++ ")"
      EOpt x -> "(opt " ++ expr x ++ ")"
      EAnd x -> "(and " ++ expr x ++ ")"
      ENot x -> "(not " ++ expr x ++ ")"
      ECapture x -> "(capture " ++ expr x ++ ")"
      ELabel l x m -> "(label@" ++ show (loc l) ++ " " ++ expr x ++ " " ++ T.unpack m ++ ")"
      EPred b c -> "(pred " ++ (if b then "T" else "F") ++ " {" ++ T.unpack (unLoc c) ++ "})"
      ETemplate l x as vs -> "(template@" ++ show (loc l) ++ " " ++ T.unpack x ++ " [" ++ unwords (map expr as) ++ "] [" ++ intercalate "," (map (T.unpack . unLoc) vs) ++ "])"
      EDiscard x -> "(discard " ++ expr x ++ ")"

leanModule :: [(String, Grammar)] -> String
leanModule gs =
  unlines
    [ "import TemplateExpansionWhole"
    , "open PegHs.TemplateExpansionWhole"
    , ""
    , "def identTable : List (String × List String) :="
    , "  " ++ list [pair (str t) (list (map str (idents t))) | t <- nub (concatMap (gramTexts . snd) gs)]
    , ""
    , "def cases : List (String × Grammar) :="
    , "  " ++ list [pair (str (T.pack n)) (grammar g) | (n, g) <- gs]
    ]
  where
    idents = map unLoc . codeVariables (Loc 0 1 1)
    grammar g =
      "{ rules := " ++ list (map rule (grammarRules g))
        ++ ", start := " ++ located (maybeToList (grammarStart g))
        ++ ", entries := " ++ located (grammarEntries g)
        ++ ", recovers := " ++ located (map snd (grammarRecovers g))
        ++ ", nomemo := " ++ located (grammarNoMemo g)
        ++ ", tokens := " ++ located (grammarTokens g)
        ++ ", trivia := " ++ located (grammarTrivia g)
        ++ ", inline := " ++ located (grammarInline g)
        ++ ", expects := " ++ located (map fst (grammarExpects g))
        ++ ", syntaxMode := " ++ (if isJust (grammarSyntax g) then "true" else "false")
        ++ " }"
    located xs = list [pair (show (loc l)) (str x) | Located l x <- xs]
    rule r =
      "{ name := " ++ str (ruleName r)
        ++ ", location := " ++ show (loc (ruleLoc r))
        ++ ", params := " ++ list [pair (str (paramName p)) (str (unLoc (paramType p))) | p <- ruleParams r]
        ++ ", templateParams := " ++ list [pair (str (templateParamName p)) (maybe "none" (\t -> "(some " ++ str t ++ ")") (templateParamType p)) | p <- ruleTemplateParams r]
        ++ ", type := " ++ str (unLoc (ruleType r))
        ++ ", annotation := " ++ maybe "none" (\l -> "(some " ++ show (loc l) ++ ")") (ruleAnnotation r)
        ++ ", alts := " ++ list (map alt (ruleAlts r))
        ++ " }"
    alt a = "{ items := " ++ list (map item (altItems a)) ++ ", action := " ++ maybe "none" (\t -> "(some " ++ str (unLoc t) ++ ")") (altAction a)
      ++ ", constructor := " ++ maybe "none" (\t -> "(some " ++ str (unLoc t) ++ ")") (altConstructor a) ++ " }"
    item i = pair (maybe "none" (\b -> "(some " ++ str b ++ ")") (itemBind i)) (expr (itemExpr i))
    expr = \case
      ELit v w -> "(.lit " ++ str v ++ " " ++ str w ++ ")"
      EClass _ w -> "(.charClass " ++ str w ++ ")"
      EAny -> ".any"
      ERef l x as -> "(.ref " ++ show (loc l) ++ " " ++ str x ++ " " ++ list (map (str . unLoc) as) ++ ")"
      EGroup alts -> "(.group " ++ list (map (list . map item) alts) ++ ")"
      EStar x -> "(.star " ++ expr x ++ ")"
      EPlus x -> "(.plus " ++ expr x ++ ")"
      EOpt x -> "(.opt " ++ expr x ++ ")"
      EAnd x -> "(.and " ++ expr x ++ ")"
      ENot x -> "(.not " ++ expr x ++ ")"
      ECapture x -> "(.capture " ++ expr x ++ ")"
      ELabel l x m -> "(.label " ++ show (loc l) ++ " " ++ expr x ++ " " ++ str m ++ ")"
      EPred b c -> "(.predicate " ++ (if b then "true" else "false") ++ " " ++ str (unLoc c) ++ ")"
      ETemplate l x as vs -> "(.template " ++ show (loc l) ++ " " ++ str x ++ " " ++ list (map expr as) ++ " " ++ list (map (str . unLoc) vs) ++ ")"
      EDiscard x -> "(.discard " ++ expr x ++ ")"
    list xs = "[" ++ intercalate ", " xs ++ "]"
    pair a b = "(" ++ a ++ ", " ++ b ++ ")"

-- Every text that the expansion may read identifiers from: the code, and the
-- parameter names that a call passes on.
gramTexts :: Grammar -> [Text]
gramTexts g = concatMap ruleTexts (grammarRules g)
  where
    ruleTexts r = map paramName (ruleParams r) ++ concatMap altTexts (ruleAlts r)
    altTexts a = map unLoc (maybeToList (altAction a)) ++ concatMap (exprTexts . itemExpr) (altItems a)
    exprTexts = \case
      ERef _ _ as -> map unLoc as
      EPred _ c -> [unLoc c]
      EGroup alts -> concatMap (concatMap (exprTexts . itemExpr)) alts
      ETemplate _ _ as vs -> concatMap exprTexts as ++ map unLoc vs
      EStar x -> exprTexts x
      EPlus x -> exprTexts x
      EOpt x -> exprTexts x
      EAnd x -> exprTexts x
      ENot x -> exprTexts x
      ECapture x -> exprTexts x
      ELabel _ x _ -> exprTexts x
      EDiscard x -> exprTexts x
      _ -> []

-- A Lean string literal.
str :: Text -> String
str t = "\"" ++ concatMap esc (T.unpack t) ++ "\""
  where
    esc '\\' = "\\\\"
    esc '"' = "\\\""
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c
      | ord c < 32 = "\\x" ++ (if ord c < 16 then "0" else "") ++ showHex (ord c) ""
      | otherwise = [c]
