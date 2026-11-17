-- The body of the differential probe of ImportResolution.lean, appended by
-- check-import-resolution.sh to the pinned `directiveRules` and `ruleRefs`
-- of Import.hs. For each case it writes the inputs of the Lean model as Lean
-- data (first argument) and the result of `resolveImports` (second argument).

data Lib
  = NoText
  | ParseError [Diagnostic]
  | NotLibrary
  | AssemblyError [Diagnostic]
  | Assembled [Diagnostic] [Rule]

-- What `library i` of `resolveImports` finds before relocating, computed by
-- the same Haskell functions.
classify :: [(FilePath, Text)] -> FilePath -> Lib
classify texts p = case lookup p texts of
  Nothing -> NoText
  Just text -> case parseTops text of
    Left ds -> ParseError ds
    Right tops
      | null [() | TDirective _ "library" _ _ <- tops] -> NotLibrary
      | otherwise -> case assemble tops of
          Left ds -> AssemblyError ds
          Right g -> Assembled (libraryErrors g) (grammarRules g)

leanString :: String -> String
leanString s = "\"" ++ concatMap esc s ++ "\""
  where
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c
      | c < ' ' = "\\x" ++ [hex (fromEnum c `div` 16), hex (fromEnum c `mod` 16)]
      | otherwise = [c]
    hex n = "0123456789abcdef" !! n

leanText :: Text -> String
leanText = leanString . T.unpack

leanList :: [String] -> String
leanList xs = "[" ++ intercalate ", " xs ++ "]"

leanLoc :: Loc -> String
leanLoc (Loc f l c) = "⟨" ++ show f ++ ", " ++ show l ++ ", " ++ show c ++ "⟩"

leanDiag :: Diagnostic -> String
leanDiag (Diagnostic l m) = "⟨" ++ leanLoc l ++ ", " ++ leanText m ++ "⟩"

leanRule :: Rule -> String
leanRule r =
  "⟨" ++ leanText (ruleName r) ++ ", " ++ leanLoc (ruleLoc r) ++ ", "
    ++ leanList (map leanText (ruleRefs r)) ++ "⟩"

leanLib :: Lib -> String
leanLib = \case
  NoText -> ".noText"
  ParseError ds -> "(.parseError " ++ leanList (map leanDiag ds) ++ ")"
  NotLibrary -> ".notLibrary"
  AssemblyError ds -> "(.assemblyError " ++ leanList (map leanDiag ds) ++ ")"
  Assembled ds rs -> "(.assembled " ++ leanList (map leanDiag ds) ++ " " ++ leanList (map leanRule rs) ++ ")"

leanCase :: String -> Grammar -> [(FilePath, Text)] -> String
leanCase name g texts =
  "  { name := " ++ leanString name
    ++ "\n  , isLibrary := " ++ (if isJust (grammarLibrary g) then "true" else "false")
    ++ "\n  , rootRules := " ++ leanList (map leanRule (grammarRules g))
    ++ "\n  , directiveNames := " ++ leanList (map leanText (directiveRules g))
    ++ "\n  , imports := " ++ leanList [ "(" ++ leanLoc l ++ ", " ++ leanString p ++ ")" | Located l p <- grammarImports g ]
    ++ "\n  , libraries := " ++ leanList [ "(" ++ leanString p ++ ", " ++ leanLib (classify texts p) ++ ")" | Located _ p <- grammarImports g ]
    ++ " }"

renderLoc :: Loc -> String
renderLoc (Loc f l c) = show f ++ ":" ++ show l ++ ":" ++ show c

render :: String -> Either [Diagnostic] Grammar -> [String]
render name = \case
  Left ds -> (name ++ " error") : [ "  " ++ renderLoc l ++ ": " ++ T.unpack m | Diagnostic l m <- ds ]
  Right g -> (name ++ " ok") : [ "  " ++ T.unpack (ruleName r) ++ " " ++ renderLoc (ruleLoc r) | r <- grammarRules g ]

ident :: Text
ident = T.unlines ["%library", "", "Ident :: Text", "Ident <- $(IdentStart IdentChar*) Sp", "", "IdentStart <- [a-zA-Z_]", "", "IdentChar <- [a-zA-Z0-9_]", "", "Sp <- [ \\t]*"]

calc :: Text
calc = T.unlines ["%module Calc.Parser", "%import lex/Ident.hpeg", "", "Assign :: (Text, Text)", "Assign <- n:Ident '=' Sp v:Ident { (n, v) }"]

cases :: [(String, Text, [(FilePath, Text)])]
cases =
  [ ("noImports", "%module M\nS <- 'a'\n", [])
  , ("calc", calc, [("lex/Ident.hpeg", ident)])
  , ("libraryRoot", ident, [])
  , ("missingFile", calc, [])
  , ("notLibrary", calc, [("lex/Ident.hpeg", "%module X\nA <- 'a'\n")])
  , ("parseError", calc, [("lex/Ident.hpeg", ident <> "X <- (\n")])
  , ("assemblyModule", calc, [("lex/Ident.hpeg", "%module M\n" <> ident)])
  , ("assemblyTwice", calc, [("lex/Ident.hpeg", ident <> "%library\n")])
  , ("assemblyVerbatim", calc, [("lex/Ident.hpeg", "%library\n%{\nimport X\n}%\nIdent <- 'a'\n")])
  , ("libraryUndefined", "%module M\n%import a.hpeg\nS <- A\n", [("a.hpeg", "%library\nA <- B\n")])
  , ("libraryDuplicate", "%module M\n%import a.hpeg\nS <- A\n", [("a.hpeg", "%library\nA <- B\nC <- 'c'\nC <- 'd'\n")])
  , ("libraryCallsRoot", "%module M\n%import a.hpeg\nS <- A Ws\nWs <- ' '*\n", [("a.hpeg", "%library\nA <- 'a' Ws\n")])
  , ("duplicateRootLibrary", calc <> "Sp <- ' '*\n", [("lex/Ident.hpeg", ident)])
  , ("duplicateLibraries", "%module M\n%import a.hpeg\n%import b.hpeg\nS <- X Y\n",
      [("a.hpeg", "%library\nX <- 'x'\nSp <- ' '\n"), ("b.hpeg", "%library\n\nY <- 'y'\nSp <- ' '\nX <- 'x'\n")])
  , ("errorsSorted", "%module M\n%import a.hpeg\n%import b.hpeg\n%import c.hpeg\n%import d.hpeg\nS <- A\n",
      [("a.hpeg", "%library\nA <- (\n"), ("c.hpeg", "%library\nC <- Z Y\nD <- W\n"), ("d.hpeg", "%module D\nD <- 'd'\n")])
  , ("order", "%module M\n%import b.hpeg\n%import a.hpeg\nS <- B A\n", [("a.hpeg", "%library\nA <- 'a'\n"), ("b.hpeg", "%library\nB <- 'b'\n")])
  , ("firstText", "%module M\n%import a.hpeg\nS <- A\n", [("a.hpeg", "%library\nA <- 'a'\n"), ("a.hpeg", "%library\nA <- (\n")])
  , ("pruning", "%module M\n%import a.hpeg\n%entry D\nS <- A\nT <- 'x'\n",
      [("a.hpeg", "%library\nA <- B / C?\nB <- 'b'\nC <- 'c' C\nUnused <- A\nD <- 'd'\nE <- D\n")])
  , ("directives", T.unlines ["%module M", "%syntax", "%import lex.hpeg", "%token Ident", "%entry Num", "%recover lab Skip", "S <- Ident ('=' ^lab) Ident"],
      [("lex.hpeg", "%library\nIdent <- [a-z]+\nSkip <- (!'\\n' .)*\nNum <- [0-9]+\nOther <- Num\n")])
  , ("template", T.unlines ["%module M", "%import list.hpeg", "S :: [Int]", "S <- List<N>", "N :: Int", "N <- '1' { 1 }"],
      [("list.hpeg", "%library\nList<p :: a> :: [a]\nList<p> <- x:p xs:(',' p)* { x : xs }\nItem <- 'i'\n")])
  , ("nested", "%module M\n%import a.hpeg\nS <- &(A) !B\n",
      [("a.hpeg", "%library\nA <- (x:B)+ ^l\nB <- C+\nC <- 'c'\nX <- 'x'\n")])
  , ("rootNameInLibrary", "%module M\n%import a.hpeg\nS <- 'a'\nT <- S\n", [("a.hpeg", "%library\nA <- 'a'\n")])
  ]

main :: IO ()
main = do
  (dataFile, outFile) <- getArgs >>= \case
    [d, o] -> pure (d, o)
    _ -> die "usage: Probe CASES.lean OUTPUT"
  results <- forM cases $ \(name, src, texts) -> case parseGrammar src of
    Left ds -> die (name ++ ": the root does not parse: " ++ show ds)
    Right g -> pure (leanCase name g texts, render name (resolveImports g texts))
  writeFile dataFile $
    "def cases : List Case := [\n" ++ intercalate ",\n" (map fst results) ++ "\n]\n\n"
      ++ "def main : IO Unit := do\n  for c in cases do\n    for line in runCase c do\n      IO.println line\n"
  writeFile outFile (unlines (concatMap snd results))
