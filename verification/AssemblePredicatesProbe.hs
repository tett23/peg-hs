-- Body of the differential probe for AssemblePredicates and the binding
-- trees. check-assemble-predicates.sh prepends the imports and the
-- Haskell spans of Assemble.hs, then runs this program twice:
--   lean      prints the Lean module AssembleProbeCases with every input
--   expected  prints what Haskell computes, in AssemblePredicatesProbe.lean's
--             format
-- Text is passed as lists of code points so that no escaping is involved.
-- The Expr serializer matches every constructor; a new constructor fails
-- the build under -Werror.

binderReasonFor :: [Top] -> Text -> Maybe Text
binderReasonFor items = binderError
  where
--BINDER-SPAN--

exportOkFor :: [Top] -> Text -> Bool
exportOkFor items = isExportItem recursiveDoEnabled arrowsEnabled
  where
--BINDER-SPAN--

codes :: Text -> String
codes t = "[" ++ intercalate ", " (map (show . ord) (T.unpack t)) ++ "]"

leanStr :: Text -> String
leanStr t = "(s " ++ codes t ++ ")"

leanList :: [String] -> String
leanList xs = "[" ++ intercalate ", " xs ++ "]"

leanTop :: Top -> String
leanTop = \case
  TDirective _ n _ a -> "(.directive " ++ leanStr n ++ " " ++ leanStr a ++ ")"
  TVerbatim _ _ -> ".verbatim"
  TAnnot _ n ps tps _ -> "(.annotation " ++ leanStr n ++ " "
    ++ leanList (map (leanStr . templateParamName) tps) ++ " "
    ++ leanList (map (leanStr . paramName) ps) ++ ")"
  TDef _ n tns alts -> "(.definition " ++ leanStr n ++ " " ++ leanList (map leanStr tns) ++ " "
    ++ leanList [leanList (map leanItem (altItems a)) | a <- alts] ++ ")"

leanItem :: Item -> String
leanItem (Item _ b e) = "(.item " ++ maybe "none" (\x -> "(some " ++ leanStr x ++ ")") b
  ++ " " ++ leanExpr e ++ ")"

leanExpr :: Expr -> String
leanExpr = \case
  ELit _ _ -> ".leaf"
  EClass _ _ -> ".leaf"
  EAny -> ".leaf"
  ERef {} -> ".leaf"
  EPred _ _ -> ".leaf"
  EGroup groups -> "(.group " ++ leanList [leanList (map leanItem g) | g <- groups] ++ ")"
  EStar e -> unary e
  EPlus e -> unary e
  EOpt e -> unary e
  EAnd e -> unary e
  ENot e -> unary e
  ECapture e -> unary e
  ELabel _ e _ -> unary e
  EDiscard e -> unary e
  ETemplate _ _ args _ -> "(.templateArgs " ++ leanList (map leanExpr args) ++ ")"
  where
    unary e = "(.unary " ++ leanExpr e ++ ")"

l0 :: Loc
l0 = Loc 0 1 1

lit :: Expr
lit = ELit "a" "'a'"

bound :: Text -> Expr -> Item
bound n = Item l0 (Just n)

plainItem :: Expr -> Item
plainItem = Item l0 Nothing

dir :: Text -> Text -> Top
dir n = TDirective l0 n l0

def :: Text -> [[Item]] -> Top
def n alts = TDef l0 n [] [Alt l0 is Nothing Nothing | is <- alts]

annot :: Text -> [Text] -> Top
annot n ps = TAnnot l0 n [Param p (Located l0 "Int") | p <- ps] [] (Located l0 "()")

modM, defS :: Top
modM = dir "module" "M"
defS = def "S" [[plainItem lit]]

names :: [Text]
names =
  [ "", "a", "A", "_", "_x", "x'", "'x", "1a", "a1", "Δ", "δx", "漢字", "ʰ", "aʰ", "x-y"
  , "case", "forall", "mdo", "rec", "proc", "do", "where", "_'", "a.b", "A.B", "A..B", ".A"
  , "A.", "Δ.Ω'", "GHC.Generics.Generic", "eq", "Eq", "ǅ", "ǅx", "Ⅰ", "x²", "١٢", "x\x200Bz"
  , "a\xA0b", "a\x3000b", "a\tb", " lab  rule ", "lab rule extra", "\x2028", "M.x'", "Ω.ǅ"
  ]

exports :: [Text]
exports =
  [ "S", "s", "T(..)", "T(a, b)", "T(a,)", "T((+))", "(+)", "(..)", "(::)", "(->)", "(-<)"
  , "(~)", "(.)", "type T", "type (+)", "pattern P", "pattern", "module X", "module x"
  , "module", "Q.do", "Q.mdo", "Q.x", "Q.T(..)", "Q.T(a)", "q.x", "Q..x", "Q.case"
  , "Q.ʰ", "mdo", "rec", "proc", "T(mdo)", "T(rec, proc)", "x -- c", "x {- c -}", "-}"
  , "where", "T (..)", "T\t( a )", "T(a b)", "T(", "bad(", "(+) x", "Δ", "ǅx", "x\ny"
  , "T(a)(b)", "T((-<))", "T(Q.x)", "_", "x'", "Δ.Ω'.T(..)", "module Δ.Ω'", "x\x3000y"
  ]

optionSets :: [Text]
optionSets =
  [ "", "RecursiveDo", "DoRec", "Arrows", "RecursiveDo, Arrows", "RecursiveDo, NoRecursiveDo"
  , "NoDoRec, DoRec", "Arrows, NoArrows", "NoRecursiveDo, RecursiveDo, NoDoRec"
  ]

languageTops :: Text -> [Top]
languageTops opts = [dir "language" opts | not (T.null opts)]

nested :: Text -> Item
nested n = plainItem (EStar (EGroup [[], [plainItem (EOpt (ECapture (EGroup [[bound n lit]])))]]))

assembleCases :: [[Top]]
assembleCases =
  [ [defS]
  , [modM, defS]
  , [modM, defS, defS]
  , [modM, annot "S" []]
  , [modM, annot "S" [], annot "S" [], defS]
  , [dir "module" "bad.name", defS]
  , [dir "module" "Δ.Ω'", defS]
  , [modM, dir "mystery" "x", defS]
  , [modM, modM, defS]
  , [dir "module" "", defS]
  , [modM, dir "syntax" "x", defS]
  , [dir "library" "", modM, defS]
  , [dir "library" "", dir "start" "S", TVerbatim l0 "x", defS]
  , [modM, dir "import" "../x.hpeg", defS]
  , [modM, dir "import" "x.hpeg", dir "import" "x.hpeg", defS]
  , [modM, dir "recover" "onlyone", defS]
  , [modM, dir "recover" "lab\x3000S", defS]
  , [modM, dir "recover" "lab S extra", defS]
  , [modM, dir "language" "lowercase", defS]
  , [modM, dir "language" "RecursiveDo, Arrows", defS]
  , [modM, dir "export" "bad(", defS]
  , [modM, dir "export" "S, T(..), (+), module X, type (+), Q.x", defS]
  , [modM, dir "export" "mdo", defS]
  , [modM, dir "language" "RecursiveDo", dir "export" "mdo", defS]
  , [modM, dir "deriving" "lowercase", defS]
  , [modM, dir "deriving" "Eq, GHC.Generics.Generic", defS]
  , [modM, dir "expect" "S \"\"", defS]
  , [modM, dir "expect" "S \"x\"", dir "expect" "S \"y\"", defS]
  , [modM, dir "message" "lab \"x\\q\"", defS]
  , [modM, dir "safe" "bad-name", defS]
  , [modM, dir "safe" "Δ", defS]
  , [modM, dir "start" "bad-name", defS]
  , [modM, dir "entry" "漢", defS]
  , [modM, dir "tabstop" "0", defS]
  , [modM, dir "tabstop" "007", defS]
  , [modM, dir "tabstop" "9223372036854775807", defS]
  , [modM, dir "tabstop" "9223372036854775808", defS]
  , [modM, TDef l0 "S" ["x"] [Alt l0 [] Nothing Nothing]]
  , [modM, TAnnot l0 "S" [] [TemplateParam "x" Nothing] (Located l0 "()"), TDef l0 "S" ["y"] [Alt l0 [] Nothing Nothing]]
  , [modM]
  , [modM, annot "P" ["case"], def "P" [[]]]
  , [modM, annot "P" ["ʰ", "aʰ", "_", "forall"], def "P" [[]]]
  , [modM, annot "P" ["rec"], dir "language" "DoRec", def "P" [[]]]
  , [modM, def "S" [[bound "case" lit]]]
  , [modM, def "S" [[bound "ʰ" lit, bound "aʰ" lit, bound "Δ" lit, bound "_" lit]]]
  , [modM, def "S" [[nested "forall"], [nested "where", bound "x" lit]]]
  , [modM, def "S" [[plainItem (ETemplate l0 "T" [EGroup [[bound "case" lit]], ELabel l0 (EGroup [[bound "of" lit]]) "lab"] [])]]]
  , [modM, def "S" [[plainItem (EDiscard (EAnd (ENot (EPlus (EGroup [[bound "let" EAny]])))))]]]
  , [modM, def "S" [[bound "mdo" lit, bound "rec" lit, bound "proc" lit]]]
  , [modM, dir "language" "RecursiveDo", def "S" [[bound "mdo" lit, bound "rec" lit, bound "proc" lit]]]
  , [modM, dir "language" "Arrows, NoArrows", def "S" [[bound "proc" lit]]]
  , [modM, dir "language" "NoDoRec, Arrows", def "S" [[bound "proc" (ERef l0 "R" []), bound "mdo" (EClass [] "[]")]]]
  , [modM, def "S" [[bound "x" (EPred True (Located l0 "x"))]], def "S" [[bound "type" lit]]]
  ]

kindOf :: Text -> String
kindOf m
  | "unknown directive %" `T.isPrefixOf` m = "unknownDirective"
  | "duplicate %" `T.isPrefixOf` m && " directive" `T.isSuffixOf` m = "duplicateDirective"
  | " needs an argument" `T.isSuffixOf` m = "missingArgument"
  | " takes no argument" `T.isSuffixOf` m = "unexpectedArgument"
  | "%library and %module" `T.isPrefixOf` m = "libraryConflict"
  | "a library cannot have %{" `T.isPrefixOf` m = "libraryVerbatim"
  | "a library cannot have %" `T.isPrefixOf` m = "libraryDirective"
  | "%import expects" `T.isPrefixOf` m = "invalidImportPath"
  | " is imported twice" `T.isSuffixOf` m = "duplicateImport"
  | "%recover expects" `T.isPrefixOf` m = "invalidRecover"
  | "%language expects" `T.isPrefixOf` m = "invalidLanguage"
  | "%module expects" `T.isPrefixOf` m = "invalidModule"
  | "%export expects" `T.isPrefixOf` m = "invalidExport"
  | "%deriving expects" `T.isPrefixOf` m = "invalidDeriving"
  | any (`T.isSuffixOf` m) [" expects a rule name and a string", " expects a label and a string", " is empty", " contains a control character"]
      || m `elem` ["unterminated literal", "invalid \\u escape", "expected '}'", "expected '{'"]
      || "unknown escape \\" `T.isPrefixOf` m = "invalidString"
  | "duplicate %expect for" `T.isPrefixOf` m || "duplicate %message for" `T.isPrefixOf` m = "duplicateString"
  | "%safe expects" `T.isPrefixOf` m = "invalidSafe"
  | " expects a rule name" `T.isSuffixOf` m = "invalidRuleName"
  | "%tabstop expects" `T.isPrefixOf` m = "invalidTabstop"
  | "so it needs a type annotation" `T.isSuffixOf` m = "missingTemplateType"
  | "has a type annotation but no definition" `T.isSuffixOf` m = "orphanAnnotation"
  | "duplicate type annotation for " `T.isPrefixOf` m = "duplicateAnnotation"
  | "duplicate definition of " `T.isPrefixOf` m = "duplicateDefinition"
  | "binding name " `T.isPrefixOf` m = "reservedBinding"
  | "parameter name " `T.isPrefixOf` m = "reservedParameter"
  | m == "the grammar has no rules" = "noRules"
  | "the template parameters of the definition" `T.isPrefixOf` m = "templateMismatch"
  | m == "missing %module directive" = "missingModule"
  | otherwise = error ("unclassified diagnostic: " ++ T.unpack m)

-- The binder named by a binder diagnostic.
binderSubject :: Text -> Maybe String
binderSubject m = do
  rest <- T.stripPrefix "binding name " m <|> T.stripPrefix "parameter name " m
  let name = fst (T.breakOn " " rest)
  pure (kindOf m ++ ":" ++ codes name)

assembleLine :: Int -> [Top] -> String
assembleLine k tops = case assemble tops of
  Right _ -> "assemble " ++ show k ++ " accepted"
  Left ds ->
    let ms = map diagMessage ds
     in "assemble " ++ show k ++ " rejected kinds=" ++ intercalate "," (nub (sort (map kindOf ms)))
          ++ " binders=" ++ intercalate "," (sort (mapMaybe binderSubject ms))

bool :: Bool -> String
bool b = if b then "true" else "false"

expected :: [String]
expected =
  [ "ident " ++ show i ++ " " ++ bool (isValidIdent n) | (i, n) <- zip [0 :: Int ..] names ]
  ++ [ "class " ++ show i ++ " " ++ bool (isClassName n) | (i, n) <- zip [0 :: Int ..] names ]
  ++ [ "module " ++ show i ++ " " ++ bool (isModuleName n) | (i, n) <- zip [0 :: Int ..] names ]
  ++ [ "modifier " ++ show i ++ " " ++ bool (startsWithModifier n) | (i, n) <- zip [0 :: Int ..] names ]
  ++ [ "words " ++ show i ++ " " ++ intercalate "," (map codes (T.words n)) | (i, n) <- zip [0 :: Int ..] names ]
  ++ [ "binder " ++ show j ++ " " ++ show i ++ " " ++ bool (isJust (binderReasonFor (languageTops o) n))
     | (j, o) <- zip [0 :: Int ..] optionSets, (i, n) <- zip [0 :: Int ..] names ]
  ++ [ "export " ++ show j ++ " " ++ show i ++ " " ++ bool (exportOkFor (languageTops o) x)
     | (j, o) <- zip [0 :: Int ..] optionSets, (i, x) <- zip [0 :: Int ..] (exports ++ names) ]
  ++ zipWith assembleLine [0 ..] assembleCases

leanModule :: [String]
leanModule =
  [ "import AssembleValidation"
  , "namespace PegHs.AssembleProbeCases"
  , "open PegHs.AssembleValidation"
  , "def s (xs : List Nat) : String := String.ofList (xs.map Char.ofNat)"
  , "def nameCases : List String := " ++ leanList (map leanStr names)
  , "def exportCases : List String := " ++ leanList (map leanStr exports)
  , "def optionSets : List (List Top) := "
      ++ leanList [leanList (map leanTop (languageTops o)) | o <- optionSets]
  , "def assembleCases : List (List Top) := " ++ leanList [leanList (map leanTop c) | c <- assembleCases]
  , "end PegHs.AssembleProbeCases"
  ]

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  case args of
    ["lean"] -> mapM_ putStrLn leanModule
    ["expected"] -> mapM_ putStrLn expected
    _ -> die "usage: lean | expected"
