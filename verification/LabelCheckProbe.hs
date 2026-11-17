{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The probe of LabelCheckModel.lean. It reads every grammar of the
-- repository and the grammars below, and keeps those that parse, resolve
-- their imports, expand their templates and pass 'check', as @peg-hs gen@
-- does before 'labelWarnings'. With the argument @lean@ it writes them as a
-- Lean module for the model; with @expect@ it writes what the real
-- 'labelWarnings' and 'stripLabelsAs' return for them, and the left
-- recursion and the nullable rules that LabelsInternal (the source of
-- Peg.Grammar.Labels under another module name) computes, in the format of
-- LabelCheckProbe.lean.
module Main (main) where

import Data.Char (ord)
import Data.List (intercalate, sort)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import LabelsInternal (leftRecursion, nullableRules)
import Numeric (showHex)
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Import (resolveImports)
import Peg.Grammar.Import.Files (readImports)
import Peg.Grammar.Labels (labelWarnings, stripLabelsAs)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (getArgs)
import System.Exit (die)
import System.FilePath (takeExtension, (</>))
import System.IO (hSetEncoding, stdout, utf8)

grammar :: [Text] -> Text
grammar rs = "%module M\n" <> T.unlines rs

inline :: [(String, Text)]
inline =
  [ ("adr0087-any", grammar ["S :: ()", "S <- ((&(!.) &('a')) 'a' ('a' &(S 'b') . ^S_any)) (((S 'b') ('b' 'b') / (S) S)) { () }"])
  , ("adr0087-group", grammar ["S :: ()", "S <- ((&(!.) &('a')) 'a' ('a' &(S 'b') . ^S_any)) (((S 'b') ('b' 'b') / (S) S)) ^S_group { () }"])
  , ("adr0087-known", grammar ["S :: ()", "S <- R ('c' ^l) { () } / 'a' 'x' { () }", "R :: ()", "R <- 'a' 'b' { () }"])
  , ("adr0088-postfix", grammar ["S :: ()", "S <- R ('c' ^l) { () } / 'a' 'x' { () }", "R :: ()", "R <- 'a' 'b' ^m { () }"])
  , ("adr0088-group", grammar ["S :: ()", "S <- R ('c' ^l) { () } / 'a' 'x' { () }", "R :: ()", "R <- ('a' ^m) 'b' { () }"])
  , ("adr0088-parens", grammar ["S :: ()", "S <- R ('c' ^l) { () } / 'a' 'x' { () }", "R :: ()", "R <- ('a') 'b' { () }"])
  , ("adr0029-nested", grammar ["S :: ()", "S <- (('b' ^l) ^l) { () } / 'c' A { () }", "A :: ()", "A <- 'a' { () }"])
  , ("prefix", grammar ["S :: ()", "S <- 'a' ('b' ^l) { () } / 'a' 'c' { () }"])
  , ("safe", grammar ["S :: ()", "S <- 'a' ('b' ^l) { () } / 'a' 'c' { () }", "%safe l"])
  , ("repetition", grammar ["S :: ()", "S <- ('x' ('y' ^l))* 'x' 'z' { () }"])
  , ("repetition-continue", grammar ["%entry T", "S :: ()", "S <- ('a' ('b' ^l)?)* 'c' { () }", "T :: ()", "T <- ('a' ('b' ^m)?)+ 'c' { () }"])
  , ("optional", grammar ["S :: ()", "S <- ('a' ^l)? 'b' { () }"])
  , ("plus", grammar ["S :: ()", "S <- ('a' ('b' ^l))+ 'a' 'c' { () }"])
  , ("other-rule", grammar ["S :: ()", "S <- A { () } / 'a' 'c' { () }", "A :: ()", "A <- 'a' ('b' ^l) { () }"])
  , ("end", grammar ["S :: ()", "S <- 'a' ('b' ^l)? { () }"])
  , ("not-repetition", grammar ["S :: ()", "S <- !((('a' ^l) 'b')*) { () }"])
  , ("and-label", grammar ["S :: ()", "S <- &('a' ('b' ^l)) 'a' 'b' { () } / 'a' 'c' { () }"])
  , ("not-label", grammar ["S :: ()", "S <- !('a' ^l) 'b' { () }"])
  , ("direct-lr", grammar ["S :: ()", "S <- E '+' 'x' { () }", "E :: ()", "E <- E '+' (T ^l) { () } / T { () }", "T :: ()", "T <- [0-9] { () }"])
  , ("direct-lr-entry", grammar ["S :: ()", "S <- E { () }", "E :: ()", "E <- E '+' (T ^l) { () } / T { () }", "T :: ()", "T <- [0-9] { () }"])
  , ("indirect-lr", grammar ["S :: ()", "S <- A { () }", "A :: ()", "A <- B 'x' ('y' ^l) { () } / 'a' { () }", "B :: ()", "B <- A 'z' { () } / 'b' { () }"])
  , ("indirect-lr-nested", grammar ["S :: ()", "S <- A { () }", "A :: ()", "A <- B 'x' ('y' ('w' ^m)) { () } / 'a' { () }", "B :: ()", "B <- A 'z' ^n { () } / 'b' { () }"])
  , ("hidden-lr", grammar ["S :: ()", "S <- A { () }", "A :: ()", "A <- N A 'x' ^l { () } / 'a' { () }", "N :: ()", "N <- 'n'? { () }"])
  , ("separator", grammar ["S :: ()", "S <- '[' V (',' (V ^l))* ']' { () }", "V :: ()", "V <- [0-9] { () }"])
  , ("start-rule", grammar ["S :: ()", "S <- A 'c' { () }", "A :: ()", "A <- 'a' ('b' ^l) { () }"])
  , ("eof", grammar ["S :: ()", "S <- (!. ^l) { () }"])
  , ("common-prefix", grammar ["S :: ()", "S <- W 'a' ('b' ^l) { () } / W 'c' { () }", "W :: ()", "W <- ' '* { () }"])
  , ( "same-arguments"
    , grammar
        [ "S :: ()", "S <- B(0) 'x' { () }", "B(n :: Int) :: ()", "B <- Bad(n) { () } / Orphan(n) { () } / P(n) { () }"
        , "Bad(n :: Int) :: ()", "Bad <- Ind(n) [ \\t] (&{ False })^l { () }", "Orphan(n :: Int) :: ()", "Orphan <- Ind(n) '=:' { () }"
        , "P(n :: Int) :: ()", "P <- Ind(n) ![ \\t] 'p' { () }", "Ind(n :: Int) :: ()", "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
        ]
    )
  , ( "different-arguments"
    , grammar
        [ "S :: ()", "S <- B(0) 'x' { () }", "B(n :: Int) :: ()", "B <- Bad(n) { () } / Orphan(n + 1) { () }"
        , "Bad(n :: Int) :: ()", "Bad <- Ind(n) [ \\t] (&{ False })^l { () }", "Orphan(n :: Int) :: ()", "Orphan <- Ind(n) '=:' { () }"
        , "Ind(n :: Int) :: ()", "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
        ]
    )
  , ( "shadowing-binding"
    , grammar
        [ "S :: ()", "S <- B(0) 'x' { () }", "B(n :: Int) :: ()", "B <- Bad(n) { () } / Orphan(n) { () }"
        , "Bad(n :: Int) :: ()", "Bad <- n:Cnt Ind(n) [ \\t] (&{ False })^l { () }", "Orphan(n :: Int) :: ()", "Orphan <- Cnt Ind(n) '=:' { () }"
        , "Cnt :: Int", "Cnt <- [0-9] { 0 }", "Ind(n :: Int) :: ()", "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
        ]
    )
  , ( "code-with-let"
    , grammar
        [ "S :: ()", "S <- B(0) 'x' { () }", "B(n :: Int) :: ()", "B <- Bad(n) { () } / Orphan(n) { () }"
        , "Bad(n :: Int) :: ()", "Bad <- Ind(let m = n in m) [ \\t] (&{ False })^l { () }", "Orphan(n :: Int) :: ()", "Orphan <- Ind(\\x -> n) '=:' { () }"
        , "Ind(n :: Int) :: ()", "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
        ]
    )
  , ( "long-code"
    , grammar
        [ "S :: ()", "S <- B(0) 'x' { () }", "B(n :: Int) :: ()", "B <- Bad(n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n) { () } / Orphan(n) { () }"
        , "Bad(n :: Int) :: ()", "Bad <- Ind(n) [ \\t] (&{ False })^l { () }", "Orphan(n :: Int) :: ()", "Orphan <- Ind(n) '=:' { () }"
        , "Ind(n :: Int) :: ()", "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
        ]
    )
  , ("constant-pred", grammar ["S :: ()", "S <- I+ !. { () }", "I :: ()", "I <- C { () } / Bad { () } / T { () }", "C :: ()", "C <- '[' 'a' (']')^l { () }", "Bad :: ()", "Bad <- '[' &{ False } { () }", "T :: ()", "T <- [a-z]+ { () }"])
  , ("not-constant-pred", grammar ["S :: ()", "S <- '[' 'a' (']')^l { () } / '[' &{ x } [a-z] { () }"])
  , ("known-second", grammar ["S :: ()", "S <- E+ !. { () }", "E :: ()", "E <- Cm { () } / T { () }", "Cm :: ()", "Cm <- '%%' (!'%%' [a-z%])* ('%%')^l { () }", "T :: ()", "T <- (!'%%' [a-z%])+ { () }"])
  , ("known-letter", grammar ["S :: ()", "S <- X+ !. { () }", "X :: ()", "X <- '[=' [0-9]+ (']')^l { () } / '[' Id ']' { () } / [a-z]+ { () }", "Id :: ()", "Id <- [a-z]+ { () }"])
  , ("known-splat", grammar ["S :: ()", "S <- A+ !. { () }", "A :: ()", "A <- Splat [a-z]+ (']')^l { () } / !Splat W { () }", "Splat :: ()", "Splat <- '**[' { () } / '*[' { () }", "W :: ()", "W <- [a-z*\\[]+ { () }"])
  , ("known-lookahead", grammar ["S :: ()", "S <- '%' 'x' ('y')^l { () } / (!'%%' [%a-z])+ { () }"])
  , ( "env"
    , T.replace "%module M\n" "%module M\n%env Int\n" $
        grammar
          [ "S :: ()", "S <- B(0) 'x' { () }", "B(n :: Int) :: ()", "B <- Bad(n) { () } / Orphan(n) { () }"
          , "Bad(n :: Int) :: ()", "Bad <- Ind(n) [ \\t] (&{ False })^l { () }", "Orphan(n :: Int) :: ()", "Orphan <- &{ _env > 0 } Ind(n) '=:' { () }"
          , "Ind(n :: Int) :: ()", "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
          ]
    )
  , ("recover-shared", grammar ["%recover a Skip", "%recover b Skip", "S :: ()", "S <- '(' ('x')^a (')')^b { () }", "Skip :: ()", "Skip <- (![)] .)* { () }"])
  , ("recover-start", grammar ["%recover a S", "%entry T", "%recover b T", "S :: ()", "S <- '(' ('x')^a T { () }", "T :: ()", "T <- 'y' ^b { () } / 'z' { () }"])
  , ("recover-rule-label", grammar ["%recover a Skip", "S :: ()", "S <- '(' X ')' { () } / '(' 'y' { () }", "X :: ()", "X <- ('x')^a { () }", "Skip :: ()", "Skip <- (![)] .)* { () }"])
  , ("recover-message", grammar ["%recover a Skip", "%message a \"an x\"", "%safe a", "S :: ()", "S <- '(' ('x')^a ')' { () } / '(' 'y' { () }", "Skip :: ()", "Skip <- (![)] .)* { () }"])
  , ("nested-groups", grammar ["S :: ()", "S <- ('a' ('b' ('c' ^l / 'd') 'e' ^m) / 'f') 'g' { () } / 'a' 'b' 'x' { () }"])
  , ("nested-captures", grammar ["S :: ()", "S <- x:$('a' $('b' ^l)) { () } / 'a' 'c' { () }"])
  , ("duplicate-alternatives", grammar ["S :: ()", "S <- 'a' ('b' ^l) { () } / 'a' ('b' ^l) { () } / 'a' 'c' { () }"])
  , ("duplicate-safe", grammar ["S :: ()", "S <- 'a' ('b' ^l) { () } / 'a' ('b' ^l) { () }"])
  , ("template-label", grammar ["S :: ()", "S <- List<'a'> ';' { () } / 'a' 'x' { () }", "List<p> :: ()", "List<p> <- p (',' (p ^item))* { () }"])
  , ("template-argument", grammar ["S :: ()", "S <- W<('a' ^l)> 'c' { () } / 'b' { () }", "W<p> :: ()", "W<p> <- p 'b' { () }"])
  , ("template-twice", grammar ["S :: ()", "S <- W<'a'> W<'b'> { () }", "W<p> :: ()", "W<p> <- p ('x' ^l) { () } / p 'y' { () }"])
  , ("entries", grammar ["%entry A", "S :: ()", "S <- A 'b' { () }", "A :: ()", "A <- 'a' ('c' ^l)? { () }"])
  , ("start", grammar ["%start A", "S :: ()", "S <- A { () }", "A :: ()", "A <- 'a' ('c' ^l)? { () }"])
  , ("classes", grammar ["S :: ()", "S <- [a-c] ([d-fx] ^l) { () } / [b-z] 'q' { () } / . 'r' { () }"])
  , ("unicode", grammar ["S :: ()", "S <- 'é' ('ü' ^l) { () } / [à-ÿ] 'q' { () } / '日本' ('語' ^m) { () }"])
  , ("empty-literal", grammar ["S :: ()", "S <- '' ('a' ^l) { () } / 'b' { () }"])
  , ("expect", grammar ["%expect l \"a b\"", "S :: ()", "S <- 'a' ('b' ^l) { () } / 'c' { () }"])
  , ("predicates", grammar ["S :: ()", "S <- &{ True } 'a' ('b' ^l) { () } / !{ False } 'a' 'c' { () } / &{ n } 'd' { () }"])
  , ("many-labels", grammar ["S :: ()", "S <- ('a' ^a) ('b' ^b) ('c' ^c) { () } / ('a' ^d) 'x' { () }", "T :: ()", "T <- (S ^e) ('y' ^f)* { () }", "%entry T"])
  ]

-- The grammar files of the repository, sorted.
hpegFiles :: FilePath -> IO [FilePath]
hpegFiles dir = do
  names <- sort <$> listDirectory dir
  concat
    <$> mapM
      ( \n -> do
          let p = dir </> n
          isDir <- doesDirectoryExist p
          if isDir && n `notElem` ["dist-newstyle", ".git", "node_modules"]
            then hpegFiles p
            else pure [p | takeExtension n == ".hpeg"]
      )
      names

-- The grammar that labelWarnings receives.
prepare :: FilePath -> Text -> IO (Maybe Grammar)
prepare file src = case parseGrammar src of
  Left _ -> pure Nothing
  Right g0 -> do
    libs <- readImports file g0
    pure $ case libs >>= resolveImports g0 >>= expandTemplates >>= (\g -> g <$ check g) of
      Left _ -> Nothing
      Right g -> Just g

cases :: IO [(String, Grammar)]
cases = do
  files <- concat <$> mapM hpegFiles ["packages", "conformance", "examples", "editors"]
  fromFiles <- mapM (\f -> TIO.readFile f >>= fmap ((,) f) . prepare f) files
  fromInline <- mapM (\(n, t) -> (,) n <$> prepare "inline.hpeg" t) inline
  pure [(n, g) | (n, Just g) <- fromFiles ++ fromInline]

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  cs <- cases
  case args of
    ["lean"] -> putStr (leanModule cs)
    ["expect"] -> mapM_ (putStr . expect) cs
    _ -> die "usage: LabelCheckProbe (lean|expect)"

-- What the model prints for a case.
expect :: (String, Grammar) -> String
expect (n, g) =
  unlines $
    ["case " ++ n]
      ++ ["warning " ++ loc l ++ " " ++ esc m | Diagnostic l m <- labelWarnings g]
      ++ stripped (stripLabelsAs "Stripped" g)
      ++ ["others " ++ show (others g == others (stripLabelsAs "Stripped" g))]
      ++ [ "direct " ++ intercalate "," (map T.unpack (S.toList direct))
         , "other " ++ intercalate "," (map T.unpack (S.toList other))
         , "growing " ++ intercalate "," [T.unpack (ruleName r) ++ ":" ++ show i | r <- grammarRules g, i <- [0 .. length (ruleAlts r) - 1], growing (ruleName r) i]
         , "nullable " ++ intercalate "," (map T.unpack (S.toList (nullableRules (grammarRules g))))
         ]
  where
    (direct, other, growing) = leftRecursion (grammarRules g)
    -- The fields stripLabelsAs may change, set to fixed values.
    others h =
      h
        { grammarModule = Located (Loc 0 0 0) ""
        , grammarRecovers = []
        , grammarSafe = []
        , grammarMessages = []
        , grammarEntries = []
        , grammarRules = [r {ruleAlts = [a {altItems = []} | a <- ruleAlts r]} | r <- grammarRules h]
        }

stripped :: Grammar -> [String]
stripped g =
  [ "module " ++ located (grammarModule g)
  , "entries " ++ intercalate "; " (map located (grammarEntries g))
  , "cleared " ++ unwords (map show [length (grammarRecovers g), length (grammarSafe g), length (grammarMessages g)])
  ]
    ++ concatMap rule (grammarRules g)
  where
    rule r = ("rule " ++ esc (ruleName r) ++ " " ++ intercalate "," (map (esc . paramName) (ruleParams r))) : concatMap alt (ruleAlts r)
    alt a = ("alt " ++ loc (altLoc a)) : ["item " ++ item i | i <- altItems a]

located :: Located Text -> String
located (Located l x) = loc l ++ " " ++ esc x

loc :: Loc -> String
loc (Loc f l c) = show f ++ ":" ++ show l ++ ":" ++ show c

item :: Item -> String
item (Item l b e) = loc l ++ "/" ++ maybe "-" esc b ++ "/" ++ expr e

expr :: Expr -> String
expr = \case
  ELit t w -> "(lit " ++ esc t ++ " " ++ esc w ++ ")"
  EClass rs w -> "(cls [" ++ intercalate "," [show (ord a) ++ "-" ++ show (ord b) | (a, b) <- rs] ++ "] " ++ esc w ++ ")"
  EAny -> "any"
  ERef l n as -> "(ref " ++ loc l ++ " " ++ esc n ++ " [" ++ intercalate "," (map located as) ++ "])"
  EGroup alts -> "(group [" ++ intercalate " | " (map (unwords . map item) alts) ++ "])"
  EStar x -> "(star " ++ expr x ++ ")"
  EPlus x -> "(plus " ++ expr x ++ ")"
  EOpt x -> "(opt " ++ expr x ++ ")"
  EAnd x -> "(and " ++ expr x ++ ")"
  ENot x -> "(not " ++ expr x ++ ")"
  ECapture x -> "(capture " ++ expr x ++ ")"
  ELabel l x n -> "(label " ++ loc l ++ " " ++ expr x ++ " " ++ esc n ++ ")"
  EPred b c -> "(pred " ++ (if b then "true" else "false") ++ " " ++ located c ++ ")"
  ETemplate l n as vs -> "(template " ++ loc l ++ " " ++ esc n ++ " [" ++ intercalate "," (map expr as) ++ "] [" ++ intercalate "," (map located vs) ++ "])"
  EDiscard x -> "(discard " ++ expr x ++ ")"

-- A quoted text, with the characters outside printable ASCII as code points.
esc :: Text -> String
esc t = "\"" ++ concatMap e (T.unpack t) ++ "\""
  where
    e '\\' = "\\\\"
    e '"' = "\\\""
    e c
      | ord c < 32 || ord c > 126 = "\\u{" ++ showHex (ord c) "" ++ "}"
      | otherwise = [c]

leanModule :: [(String, Grammar)] -> String
leanModule cs =
  unlines $
    [ "import LabelCheckModel"
    , "open PegHs.LabelCheck"
    , ""
    , "def hc (n : Nat) : HChar := ⟨min n maxCode, Nat.min_le_right _ _⟩"
    , ""
    ]
      ++ concat (zipWith def [0 :: Int ..] cs)
      ++ ["def cases : List (String × Grammar) :=", "  " ++ list [pair (str (T.pack n)) ("case" ++ show i) | (i, (n, _)) <- zip [0 :: Int ..] cs]]
  where
    def i (_, g) = ["def case" ++ show i ++ " : Grammar :=", "  " ++ gram g, ""]
    gram g =
      "{ module := " ++ lloc (grammarModule g)
        ++ ", start := " ++ maybe "none" (\s -> "(some " ++ lloc s ++ ")") (grammarStart g)
        ++ ", entries := " ++ list (map lloc (grammarEntries g))
        ++ ", recovers := " ++ list [pair (lloc a) (lloc b) | (a, b) <- grammarRecovers g]
        ++ ", safe := " ++ list (map lloc (grammarSafe g))
        ++ ", messages := " ++ list [pair (lloc a) (lloc b) | (a, b) <- grammarMessages g]
        ++ ", rules := " ++ list (map rule (grammarRules g))
        ++ ", other := [] }"
    rule r =
      "{ name := " ++ str (ruleName r)
        ++ ", params := " ++ list (map (str . paramName) (ruleParams r))
        ++ ", alts := " ++ list (map alt (ruleAlts r))
        ++ ", other := [] }"
    alt a = "{ loc := " ++ lc (altLoc a) ++ ", items := " ++ list (map litem (altItems a)) ++ ", other := [] }"
    litem (Item l b e) = "(" ++ lc l ++ ", " ++ maybe "none" (\x -> "some " ++ str x) b ++ ", " ++ lexpr e ++ ")"
    lexpr = \case
      ELit t w -> "(.lit " ++ str t ++ " " ++ str w ++ ")"
      EClass rs w -> "(.cls " ++ list [pair ("hc " ++ show (ord a)) ("hc " ++ show (ord b)) | (a, b) <- rs] ++ " " ++ str w ++ ")"
      EAny -> ".any"
      ERef l n as -> "(.ref " ++ lc l ++ " " ++ str n ++ " " ++ list (map lloc as) ++ ")"
      EGroup alts -> "(.group " ++ list (map (list . map litem) alts) ++ ")"
      EStar x -> "(.star " ++ lexpr x ++ ")"
      EPlus x -> "(.plus " ++ lexpr x ++ ")"
      EOpt x -> "(.opt " ++ lexpr x ++ ")"
      EAnd x -> "(.and " ++ lexpr x ++ ")"
      ENot x -> "(.not " ++ lexpr x ++ ")"
      ECapture x -> "(.capture " ++ lexpr x ++ ")"
      ELabel l x n -> "(.label " ++ lc l ++ " " ++ lexpr x ++ " " ++ str n ++ ")"
      EPred b c -> "(.pred " ++ (if b then "true" else "false") ++ " " ++ lloc c ++ ")"
      ETemplate l n as vs -> "(.template " ++ lc l ++ " " ++ str n ++ " " ++ list (map lexpr as) ++ " " ++ list (map lloc vs) ++ ")"
      EDiscard x -> "(.discard " ++ lexpr x ++ ")"
    lc (Loc f l c) = "⟨" ++ show f ++ ", " ++ show l ++ ", " ++ show c ++ "⟩"
    lloc (Located l x) = pair (lc l) (str x)
    list xs = "[" ++ intercalate ", " xs ++ "]"
    pair a b = "(" ++ a ++ ", " ++ b ++ ")"

-- A Lean string literal.
str :: Text -> String
str t = "\"" ++ concatMap e (T.unpack t) ++ "\""
  where
    e '\\' = "\\\\"
    e '"' = "\\\""
    e '\n' = "\\n"
    e '\t' = "\\t"
    e c
      | ord c < 32 = "\\x" ++ (if ord c < 16 then "0" else "") ++ showHex (ord c) ""
      | otherwise = [c]
