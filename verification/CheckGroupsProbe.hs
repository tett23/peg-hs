{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The probe of CheckGroupsModel.lean. It reads every grammar of the
-- repository and the grammars below, and keeps those that parse, resolve
-- their imports and expand their templates, as @peg-hs gen@ does before
-- 'check'; each grammar of the repository also gives a variant without its
-- first rule. With the argument @lean@ it writes them as a Lean module for
-- the model, with what the model takes from 'classify', 'codeVariables',
-- 'isUpper' and 'toUpper'; with @expect@ it writes what the real 'check' and
-- 'checkLibrary' return for them, and what the functions of CheckInternal
-- (the source of Peg.Grammar.Check under another module name) return, in the
-- format of CheckGroupsProbe.lean.
module Main (main) where

import qualified CheckInternal as CI
import Data.Char (isUpper, ord, toUpper)
import Data.List (intercalate, nub, sort)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Numeric (showHex)
import Peg.Grammar
import Peg.Grammar.Check (Analysis (..), check, checkLibrary)
import Peg.Grammar.Import (resolveImports)
import Peg.Grammar.Import.Files (readImports)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import Peg.Grammar.Types
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (getArgs)
import System.Exit (die)
import System.FilePath (takeExtension, (</>))
import System.IO (hSetEncoding, stdout, utf8)

grammar :: [Text] -> Text
grammar rs = "%module M\n" <> T.unlines rs

-- Grammars for each error of check. Each must parse and expand.
inline :: [(String, Text)]
inline =
  [ ("ok", grammar ["S :: ()", "S <- 'a' { () }"])
  , ("undefined", grammar ["S :: ()", "S <- A { () }"])
  , ("undefined-directives", grammar ["%start X", "%entry Y", "%nomemo Z", "%expect W \"w\"", "S :: ()", "S <- 'a' { () }"])
  , ("arity-none", grammar ["S :: ()", "S <- A(1) { () }", "A :: ()", "A <- 'a' { () }"])
  , ("arity-some", grammar ["S :: ()", "S <- A { () } / A(1, 2) { () }", "A(n :: Int) :: ()", "A <- 'a' { () }"])
  , ("entry-params", grammar ["%entry A", "S :: ()", "S <- A(1) { () }", "A(n :: Int) :: ()", "A <- 'a' { () }"])
  , ("start-params", grammar ["%start A", "S :: ()", "S <- A(1) { () }", "A(n :: Int) :: ()", "A <- 'a' { () }"])
  , ("entry-twice", grammar ["%entry A", "%entry A", "S :: ()", "S <- 'b' { () }", "A :: ()", "A <- 'a' { () }"])
  , ("unreachable", grammar ["S :: ()", "S <- 'a' { () }", "A :: ()", "A <- B { () }", "B :: ()", "B <- A { () }"])
  , ("reachable-deep", grammar ["%entry E", "%recover l R", "S :: ()", "S <- A ('x' ^l) { () }", "A :: ()", "A <- B { () }", "B :: ()", "B <- 'b' { () }", "E :: ()", "E <- F { () }", "F :: ()", "F <- 'f' { () }", "R :: ()", "R <- Q { () }", "Q :: ()", "Q <- 'q' { () }", "U :: ()", "U <- U { () }"])
  , ("repetition", grammar ["S :: ()", "S <- ('a'?)* { () } / (&'a')+ { () } / (N (('b'?)+)*) { () }", "N :: ()", "N <- 'n'? { () }"])
  , ("binding-reserved", grammar ["S :: ()", "S <- _x:A { () }", "A :: ()", "A <- 'a' { () }"])
  , ("binding-no-value", grammar ["S :: ()", "S <- x:'a' { () } / ('b' y:'c') { () }"])
  , ("binding-twice", grammar ["S :: ()", "S <- x:A x:A y:A y:A { () }", "A :: Int", "A <- 'a' { 1 }"])
  , ("omission-none", grammar ["S :: Int", "S <- 'a'"])
  , ("omission-two", grammar ["S :: Int", "S <- A A", "A :: Int", "A <- 'a' { 1 }"])
  , ("omission-unit", grammar ["S :: ()", "S <- U U", "U :: ()", "U <- 'u' { () }"])
  , ("group-binding", grammar ["S :: ()", "S <- ('a' _y:A ('b' z:'c')) { () }", "A :: Int", "A <- 'a' { 1 }"])
  , ("reference-right", grammar ["S :: ()", "S <- &{ x > 0 } x:A { () }", "A :: Int", "A <- 'a' { 1 }"])
  , ("reference-group", grammar ["S :: ()", "S <- (x:A) &{ x > 0 } { () }", "A :: Int", "A <- 'a' { 1 }"])
  , ("reference-other", grammar ["S :: ()", "S <- x:A { () } / B(x) { () }", "B(n :: Int) :: ()", "B <- 'b' { () }", "A :: Int", "A <- 'a' { 1 }"])
  , ("reference-params", grammar ["S :: ()", "S <- B(1) { () }", "B(n :: Int) :: ()", "B <- &{ n > 0 } n2:A { () } / n2:A &{ n2 > n } { () }", "A :: Int", "A <- 'a' { 1 }"])
  , ("constructor-syntax", "%module M\n%syntax\nS <- 'a' @Foo\n")
  , ("constructor-annotation", grammar ["S :: ()", "S <- 'a' { () } @Foo"])
  , ("constructor-action", grammar ["S <- 'a' { () } @Foo"])
  , ("constructor-unit", grammar ["S <- 'a' @Foo"])
  , ("constructor-lower", grammar ["S <- A B @foo / A @Bar", "A :: Int", "A <- 'a' { 1 }", "B :: Int", "B <- 'b' { 1 }"])
  , ("constructor-twice", grammar ["S <- A B @Foo / A @Foo", "A :: Int", "A <- 'a' { 1 }", "B :: Int", "B <- 'b' { 1 }"])
  , ("constructor-other", grammar ["S <- T A B @Foo / A @Bar", "T <- A B @Foo / B @Baz", "A :: Int", "A <- 'a' { 1 }", "B :: Int", "B <- 'b' { 1 }"])
  , ("constructor-type", grammar ["S <- T A B @T / A @Bar", "T <- A B @Q / B @Baz", "A :: Int", "A <- 'a' { 1 }", "B :: Int", "B <- 'b' { 1 }"])
  , ("type-names", grammar ["S <- expr Expr", "expr <- A B / B", "Expr <- A B / A", "A :: Int", "A <- 'a' { 1 }", "B :: Int", "B <- 'b' { 1 }"])
  , ("constructor-unknown", grammar ["S <- X B @foo / B", "B :: Int", "B <- 'b' { 1 }"])
  , ("param-lr", grammar ["S :: ()", "S <- A(1) { () }", "A(n :: Int) :: ()", "A <- A(n) 'x' { () } / 'y' { () }"])
  , ("syntax-names", "%module M\n%syntax\n%token tok\n%inline Inl\nS <- expr Expr tok Tok Inl inl\nexpr <- 'a'\nExpr <- 'b'\ntok <- 'c'\nTok <- 'd'\nInl <- 'e'\ninl <- 'f'\n")
  , ("hygiene", "%module M\n%{\npeg'x = 1\ndata Peg'T = T\n  peg'y = 2\nimport qualified Data.Map as PegRt\nimport X as PegPrelude (y)\nPeg'z :: Int\n}%\nS :: ()\nS <- 'a' { () }\n")
  , ("language", grammar ["%language RebindableSyntax", "%language LambdaCase", "S :: ()", "S <- 'a' { () }"])
  , ("nomemo-lr", grammar ["%nomemo E", "%nomemo T", "S :: ()", "S <- E { () }", "E :: ()", "E <- E 'x' { () } / T { () }", "T :: ()", "T <- 'y' { () }"])
  , ("syntax-missing", grammar ["%token S", "%trivia S", "%inline S", "S :: ()", "S <- 'a' { () }"])
  , ("syntax-checks", "%module M\n%syntax\n%token T\n%trivia U\n%inline T\n%inline S\n%entry E\n%inline E\nS <- T U E\nT <- 'a'\nU <- 'b'\nE <- 'c'\n")
  , ("recover", grammar ["%recover l R", "%recover l Q", "%recover m P", "%recover n X", "%safe k", "%message j \"m\"", "S :: ()", "S <- ('a' ^l) R Q { () }", "R :: ()", "R <- 'r' { () }", "Q :: ()", "Q <- 'q' { () }", "P(n :: Int) :: ()", "P <- 'p' { () }"])
  , ("recover-lr", grammar ["%recover l R", "S :: ()", "S <- ('a' ^l) { () }", "R :: ()", "R <- S { () }"])
  , ("recover-nullable", grammar ["%recover l R", "S :: ()", "S <- A S 'x' { () } / 'y' { () }", "A :: ()", "A <- ('a' ^l) { () }", "R :: ()", "R <- 'r'? { () }"])
  , ("indirect-lr", grammar ["S :: ()", "S <- A { () }", "A :: ()", "A <- B 'x' { () } / 'a' { () }", "B :: ()", "B <- N A 'z' { () } / 'b' { () }", "N :: ()", "N <- 'n'? { () }"])
  , ("lr-groups", grammar ["S :: ()", "S <- (&S 'a')* 'b' { () } / !S 'c' { () } / $(S) 'd' { () }"])
  , ("empty-literal", grammar ["S :: ()", "S <- '' S { () } / 'a' { () }"])
  , ("templates", grammar ["S :: ()", "S <- List<'a'> List<B> { () }", "B :: ()", "B <- 'b' { () }", "List<p> :: ()", "List<p> <- p (',' p)* { () }"])
  , ("many", grammar ["%start A", "%entry A", "%entry Z", "%nomemo A", "S :: ()", "S <- A(1) Z x:'q' { x }", "A :: ()", "A <- A ('x'?)* _y:B { () }", "B :: Int", "B <- 'b'"])
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

-- The grammar that check receives.
prepare :: FilePath -> Text -> IO (Maybe Grammar)
prepare file src = case parseGrammar src of
  Left _ -> pure Nothing
  Right g0 -> do
    libs <- readImports file g0
    pure $ case libs >>= resolveImports g0 >>= expandTemplates of
      Left _ -> Nothing
      Right g -> Just g

cases :: IO [(String, Grammar)]
cases = do
  files <- concat <$> mapM hpegFiles ["packages", "conformance", "examples", "editors"]
  fromFiles <- mapM (\f -> TIO.readFile f >>= fmap ((,) f) . prepare f) files
  fromInline <- mapM (\(n, t) -> (,) n <$> prepare "inline.hpeg" t) inline
  case [n | (n, Nothing) <- fromInline] of
    [] -> pure ()
    bad -> die ("inline grammars that do not parse or expand: " ++ unwords bad)
  let kept = [(n, g) | (n, Just g) <- fromFiles]
      variants = [(n ++ "#drop-first", g {grammarRules = drop 1 (grammarRules g)}) | (n, g) <- kept, length (grammarRules g) > 1]
      written = [(n, g) | (n, Just g) <- fromInline]
      -- The branches of check that parsing does not reach: a library and
      -- a grammar without rules, as values.
      branches =
        concat
          [ [(n ++ "#library", g {grammarLibrary = Just (Loc 0 1 1)}), (n ++ "#no-rules", g {grammarRules = []})]
          | (n, g) <- take 2 written ++ take 2 kept
          ]
  pure (kept ++ variants ++ written ++ branches)

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  cs <- cases
  case args of
    ["lean"] -> putStr (leanModule cs)
    ["expect"] -> mapM_ (putStr . expect) cs
    _ -> die "usage: CheckGroupsProbe (lean|expect)"

nameSet :: S.Set Text -> String
nameSet = intercalate "," . map esc . S.toList

diags :: String -> [Diagnostic] -> [String]
diags tag ds = [tag ++ " " ++ loc l ++ " " ++ esc m | Diagnostic l m <- ds]

-- What the model prints for a case.
expect :: (String, Grammar) -> String
expect (n, g) =
  unlines $
    ["case " ++ n]
      ++ either (diags "error") okLines (check g)
      ++ diags "library" (checkLibrary g)
      ++ [ "nullable-rec " ++ nameSet (CI.nullableRulesWith recovery rules)
         , "lr-rec " ++ nameSet (CI.leftRecursiveRules recovery rules)
         ]
      ++ concat
        [ diags ("repetition " ++ esc (ruleName r)) (CI.repetitionErrors nullable r)
            ++ diags ("alt " ++ esc (ruleName r)) (CI.altErrors True units (CI.discardingRules g) (CI.valuedRules g classes) (classUnknown classes) r)
            ++ diags ("altlib " ++ esc (ruleName r)) (CI.altErrors False units (CI.discardingRules g) (CI.valuedRules g classes) (classUnknown classes) r)
            ++ diags ("binding " ++ esc (ruleName r)) (CI.bindingReferenceErrors r)
        | r <- rules
        ]
      ++ diags "constructor" (CI.constructorErrors g classes)
      ++ diags "syntax-name" (CI.syntaxNameErrors g)
      ++ diags "hygiene" (concatMap CI.hygieneErrors (grammarVerbatim g))
  where
    rules = grammarRules g
    recovery = M.fromList [(unLoc l, unLoc r) | (l, r) <- grammarRecovers g]
    nullable = CI.nullableRules rules
    classes = classify g
    units = classUnits classes
    okLines a =
        [ "ok " ++ esc (analysisStart a)
        , "lr " ++ nameSet (analysisLeftRecursive a)
        , "nullable " ++ nameSet (analysisNullable a)
        , "units " ++ nameSet (analysisUnit a)
        ]

loc :: Loc -> String
loc (Loc f l c) = show f ++ ":" ++ show l ++ ":" ++ show c

-- A quoted text, with the characters outside printable ASCII as code points.
esc :: Text -> String
esc t = "\"" ++ concatMap e (T.unpack t) ++ "\""
  where
    e '\\' = "\\\\"
    e '"' = "\\\""
    e c
      | ord c < 32 || ord c > 126 = "\\u{" ++ showHex (ord c) "" ++ "}"
      | otherwise = [c]

-- The pieces of code of a grammar, which codeVariables may read.
grammarCodes :: Grammar -> [Located Text]
grammarCodes g = nub (concat [maybe [] pure (altAction a) ++ concatMap (exprCodes . itemExpr) (altItems a) | r <- grammarRules g, a <- ruleAlts r])
  where
    exprCodes = \case
      EPred _ c -> [c]
      ERef _ _ args -> args
      ETemplate _ _ args vs -> vs ++ concatMap exprCodes args
      EGroup alts -> concatMap (concatMap (exprCodes . itemExpr)) alts
      EStar x -> exprCodes x
      EPlus x -> exprCodes x
      EOpt x -> exprCodes x
      EAnd x -> exprCodes x
      ENot x -> exprCodes x
      ECapture x -> exprCodes x
      ELabel _ x _ -> exprCodes x
      EDiscard x -> exprCodes x
      _ -> []

-- The characters whose isUpper and toUpper the model may read.
grammarChars :: Grammar -> String
grammarChars g =
  nub $
    concatMap T.unpack ([ruleName r | r <- grammarRules g] ++ [unLoc c | r <- grammarRules g, a <- ruleAlts r, Just c <- [altConstructor a]])

leanModule :: [(String, Grammar)] -> String
leanModule cs =
  unlines $
    [ "import CheckGroupsModel"
    , "open PegHs.CheckGroups"
    , "open PegHs.LabelCheck (Loc Expr Item)"
    , ""
    , "def hc (n : Nat) : PegHs.LabelCheck.HChar := ⟨min n PegHs.LabelCheck.maxCode, Nat.min_le_right _ _⟩"
    , ""
    , "structure Data where"
    , "  units : List String"
    , "  unknown : List String"
    , "  generated : List String"
    , "  dataTypes : List DataType"
    , "  codes : List ((Loc × String) × List (Loc × String))"
    , "  upper : List Nat"
    , "  toUpper : List (Nat × Nat)"
    , ""
    ]
      ++ concat (zipWith def [0 :: Int ..] cs)
      ++ ["def cases : List (String × Grammar × Data) :=", "  " ++ list [triple (str (T.pack n)) ("case" ++ show i) ("data" ++ show i) | (i, (n, _)) <- zip [0 :: Int ..] cs]]
  where
    def i (_, g) =
      [ "def case" ++ show i ++ " : Grammar :=", "  " ++ gram g, ""
      , "def data" ++ show i ++ " : Data :=", "  " ++ dat g, ""
      ]
    triple a b c = "(" ++ a ++ ", " ++ b ++ ", " ++ c ++ ")"
    dat g =
      let c = classify g
       in "{ units := " ++ list (map str (S.toList (classUnits c)))
            ++ ", unknown := " ++ list (map str (S.toList (classUnknown c)))
            ++ ", generated := " ++ list [str n | (n, Generated _) <- M.toList (classRules c)]
            ++ ", dataTypes := " ++ list (map dataType (classDataTypes c))
            ++ ", codes := " ++ list [pair (pair (lc l) (str x)) (list (map lloc (codeVariables l x))) | Located l x <- grammarCodes g]
            ++ ", upper := " ++ list [show (ord ch) | ch <- grammarChars g, isUpper ch]
            ++ ", toUpper := " ++ list [pair (show (ord ch)) (show (ord (toUpper ch))) | ch <- grammarChars g, toUpper ch /= ch]
            ++ " }"
    dataType d =
      "{ rule := " ++ str (dataRule d) ++ ", name := " ++ str (dataName d)
        ++ ", constructors := " ++ list [ "{ name := " ++ str (conName k) ++ ", nameLoc := " ++ maybe "none" (\l -> "some " ++ lc l) (conNameLoc k) ++ ", altLoc := " ++ lc (conAltLoc k) ++ " }" | k <- dataConstructors d]
        ++ " }"
    gram g =
      "{ library := " ++ maybe "none" (\l -> "some " ++ lc l) (grammarLibrary g)
        ++ ", start := " ++ maybe "none" (\s -> "(some " ++ lloc s ++ ")") (grammarStart g)
        ++ ", entries := " ++ list (map lloc (grammarEntries g))
        ++ ", noMemo := " ++ list (map lloc (grammarNoMemo g))
        ++ ", languages := " ++ list (map lloc (grammarLanguages g))
        ++ ", syntaxLoc := " ++ maybe "none" (\l -> "some " ++ lc l) (grammarSyntax g)
        ++ ", tokens := " ++ list (map lloc (grammarTokens g))
        ++ ", trivia := " ++ list (map lloc (grammarTrivia g))
        ++ ", inline := " ++ list (map lloc (grammarInline g))
        ++ ", recovers := " ++ list [pair (lloc a) (lloc b) | (a, b) <- grammarRecovers g]
        ++ ", safe := " ++ list (map lloc (grammarSafe g))
        ++ ", expects := " ++ list [pair (lloc a) (lloc b) | (a, b) <- grammarExpects g]
        ++ ", messages := " ++ list [pair (lloc a) (lloc b) | (a, b) <- grammarMessages g]
        ++ ", verbatim := " ++ list (map lloc (grammarVerbatim g))
        ++ ", rules := " ++ list (map rule (grammarRules g))
        ++ " }"
    rule r =
      "{ name := " ++ str (ruleName r)
        ++ ", loc := " ++ lc (ruleLoc r)
        ++ ", params := " ++ list (map (str . paramName) (ruleParams r))
        ++ ", templateParams := " ++ show (length (ruleTemplateParams r))
        ++ ", annotation := " ++ maybe "none" (\l -> "some " ++ lc l) (ruleAnnotation r)
        ++ ", alts := " ++ list (map alt (ruleAlts r))
        ++ " }"
    alt a =
      "{ loc := " ++ lc (altLoc a)
        ++ ", items := " ++ list (map litem (altItems a))
        ++ ", action := " ++ maybe "none" (\x -> "some " ++ lloc x) (altAction a)
        ++ ", constructor := " ++ maybe "none" (\x -> "some " ++ lloc x) (altConstructor a)
        ++ " }"
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
