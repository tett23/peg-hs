import VerbatimChunks
namespace PegHs.MetaExecution.Verbatim47Data
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def chunk0 : List Char := "\nimport Data.Char (chr, digitToInt, isHexDigit, isSpace)\nimport ".toList
def chunk1 : List Char := "Data.Text (Text)\nimport qualified Data.Text as T\nimport Peg.Gram".toList
def chunk2 : List Char := "mar\nimport Peg.Grammar.Assemble\nimport Peg.Runtime (Pos (..), Sp".toList
def chunk3 : List Char := "an (..))\n\nhere :: Span -> Loc\nhere s = Loc 0 (posLine (spanStart".toList
def chunk4 : List Char := " s)) (posColumn (spanStart s))\n\nfirstChar :: Text -> Char\nfirstC".toList
def chunk5 : List Char := "har = T.foldr const ' '\n\n-- Characters of the inside of a litera".toList
def chunk6 : List Char := "l or class, with escapes decoded.\n-- The flag marks an unescaped".toList
def chunk7 : List Char := " '-', which can form a range in a class.\ntokens :: Text -> [(Cha".toList
def chunk8 : List Char := "r, Bool)]\ntokens = go . T.unpack\n  where\n    -- Recovery (ADR 00".toList
def chunk9 : List Char := "35) can reach here with an invalid escape.\n    go ('\\\\' : 'u' : ".toList
def chunk10 : List Char := "'{' : rest) =\n      let (h, rest') = span isHexDigit rest\n      ".toList
def chunk11 : List Char := "    n = foldl (\\m d -> m * 16 + toInteger (digitToInt d)) 0 h\n  ".toList
def chunk12 : List Char := "     in (if n <= 0x10FFFF then chr (fromInteger n) else '\\xFFFD'".toList
def chunk13 : List Char := ", False) : go (drop 1 rest')\n    go ('\\\\' : c : rest) = (escape ".toList
def chunk14 : List Char := "c, False) : go rest\n    go (c : rest) = (c, c == '-') : go rest\n".toList
def chunk15 : List Char := "    go [] = []\n    escape c = case c of\n      'n' -> '\\n'\n      ".toList
def chunk16 : List Char := "'t' -> '\\t'\n      'r' -> '\\r'\n      _ -> c\n\ninside :: Text -> Te".toList
def chunk17 : List Char := "xt\ninside = T.drop 1 . T.dropEnd 1\n\ndecodeLiteral :: Text -> Tex".toList
def chunk18 : List Char := "t\ndecodeLiteral = T.pack . map fst . tokens . inside\n\nclassRange".toList
def chunk19 : List Char := "s :: Text -> [(Char, Char)]\nclassRanges = go . tokens . inside\n ".toList
def chunk20 : List Char := " where\n    go ((a, _) : (_, True) : (b, _) : rest) = (a, b) : go".toList
def chunk21 : List Char := " rest\n    go ((a, _) : rest) = (a, a) : go rest\n    go [] = []\n\n".toList
def chunk22 : List Char := "validHex :: Text -> Bool\nvalidHex h = not (T.null h) && T.foldl'".toList
def chunk23 : List Char := " (\\n d -> n * 16 + toInteger (digitToInt d)) 0 h <= (0x10FFFF ::".toList
def chunk24 : List Char := " Integer)\n\n-- Every range of a class item is non-empty.\nnonEmpty".toList
def chunk25 : List Char := "Ranges :: Text -> Bool\nnonEmptyRanges item = all (uncurry (<=)) ".toList
def chunk26 : List Char := "(classRanges (T.concat [T.pack \"[\", item, T.pack \"]\"]))\n\nparamFo".toList
def chunk27 : List Char := "rmMessage :: Text\nparamFormMessage = T.pack \"expected a paramete".toList
def chunk28 : List Char := "r of the form name :: Type\"\n\nparamError :: Loc -> Text -> Maybe ".toList
def chunk29 : List Char := "Text\nparamError l c = either Just (const Nothing) (toParam (Loca".toList
def chunk30 : List Char := "ted l c))\n\nparam :: Loc -> Text -> Param\nparam l c = either (con".toList
def chunk31 : List Char := "st (Param T.empty (Located l c))) id (toParam (Located l c))\n\n--".toList
def chunk32 : List Char := " The limit on the nesting of expressions (ADR 0080).\nmaxDepth ::".toList
def chunk33 : List Char := " Int\nmaxDepth = 256\n\n-- A construct one level deeper than what i".toList
def chunk34 : List Char := "t contains.\ndeeper :: (a -> Expr) -> (a, Int) -> (Expr, Int)\ndee".toList
def chunk35 : List Char := "per f (x, n) = (f x, n + 1)\n\n-- The items of the sequences of a ".toList
def chunk36 : List Char := "group, and the levels of the deepest.\nwithDepth :: [[(Item, Int)".toList
def chunk37 : List Char := "]] -> ([[Item]], Int)\nwithDepth ss = (map (map fst) ss, maximum ".toList
def chunk38 : List Char := "(0 : map snd (concat ss)))\n\napplyOp :: Expr -> Char -> Expr\nappl".toList
def chunk39 : List Char := "yOp e c = case c of\n  '*' -> EStar e\n  '+' -> EPlus e\n  _ -> EOp".toList
def chunk40 : List Char := "t e\n".toList
def suffix41 : List Char := ['}', '%']
theorem rest41 : verbatimRest suffix41 = ['}', '%'] := rfl
def suffix40 : List Char := chunk40 ++ suffix41
theorem safe40 : safeChunk chunk40 = true := by decide +kernel
theorem rest40 : verbatimRest suffix40 = ['}', '%'] := by
  rw [suffix40, invariant1_safe_chunk chunk40 suffix41 safe40]
  exact rest41
def suffix39 : List Char := chunk39 ++ suffix40
theorem safe39 : safeChunk chunk39 = true := by decide +kernel
theorem rest39 : verbatimRest suffix39 = ['}', '%'] := by
  rw [suffix39, invariant1_safe_chunk chunk39 suffix40 safe39]
  exact rest40
def suffix38 : List Char := chunk38 ++ suffix39
theorem safe38 : safeChunk chunk38 = true := by decide +kernel
theorem rest38 : verbatimRest suffix38 = ['}', '%'] := by
  rw [suffix38, invariant1_safe_chunk chunk38 suffix39 safe38]
  exact rest39
def suffix37 : List Char := chunk37 ++ suffix38
theorem safe37 : safeChunk chunk37 = true := by decide +kernel
theorem rest37 : verbatimRest suffix37 = ['}', '%'] := by
  rw [suffix37, invariant1_safe_chunk chunk37 suffix38 safe37]
  exact rest38
def suffix36 : List Char := chunk36 ++ suffix37
theorem safe36 : safeChunk chunk36 = true := by decide +kernel
theorem rest36 : verbatimRest suffix36 = ['}', '%'] := by
  rw [suffix36, invariant1_safe_chunk chunk36 suffix37 safe36]
  exact rest37
def suffix35 : List Char := chunk35 ++ suffix36
theorem safe35 : safeChunk chunk35 = true := by decide +kernel
theorem rest35 : verbatimRest suffix35 = ['}', '%'] := by
  rw [suffix35, invariant1_safe_chunk chunk35 suffix36 safe35]
  exact rest36
def suffix34 : List Char := chunk34 ++ suffix35
theorem safe34 : safeChunk chunk34 = true := by decide +kernel
theorem rest34 : verbatimRest suffix34 = ['}', '%'] := by
  rw [suffix34, invariant1_safe_chunk chunk34 suffix35 safe34]
  exact rest35
def suffix33 : List Char := chunk33 ++ suffix34
theorem safe33 : safeChunk chunk33 = true := by decide +kernel
theorem rest33 : verbatimRest suffix33 = ['}', '%'] := by
  rw [suffix33, invariant1_safe_chunk chunk33 suffix34 safe33]
  exact rest34
def suffix32 : List Char := chunk32 ++ suffix33
theorem safe32 : safeChunk chunk32 = true := by decide +kernel
theorem rest32 : verbatimRest suffix32 = ['}', '%'] := by
  rw [suffix32, invariant1_safe_chunk chunk32 suffix33 safe32]
  exact rest33
def suffix31 : List Char := chunk31 ++ suffix32
theorem safe31 : safeChunk chunk31 = true := by decide +kernel
theorem rest31 : verbatimRest suffix31 = ['}', '%'] := by
  rw [suffix31, invariant1_safe_chunk chunk31 suffix32 safe31]
  exact rest32
def suffix30 : List Char := chunk30 ++ suffix31
theorem safe30 : safeChunk chunk30 = true := by decide +kernel
theorem rest30 : verbatimRest suffix30 = ['}', '%'] := by
  rw [suffix30, invariant1_safe_chunk chunk30 suffix31 safe30]
  exact rest31
def suffix29 : List Char := chunk29 ++ suffix30
theorem safe29 : safeChunk chunk29 = true := by decide +kernel
theorem rest29 : verbatimRest suffix29 = ['}', '%'] := by
  rw [suffix29, invariant1_safe_chunk chunk29 suffix30 safe29]
  exact rest30
def suffix28 : List Char := chunk28 ++ suffix29
theorem safe28 : safeChunk chunk28 = true := by decide +kernel
theorem rest28 : verbatimRest suffix28 = ['}', '%'] := by
  rw [suffix28, invariant1_safe_chunk chunk28 suffix29 safe28]
  exact rest29
def suffix27 : List Char := chunk27 ++ suffix28
theorem safe27 : safeChunk chunk27 = true := by decide +kernel
theorem rest27 : verbatimRest suffix27 = ['}', '%'] := by
  rw [suffix27, invariant1_safe_chunk chunk27 suffix28 safe27]
  exact rest28
def suffix26 : List Char := chunk26 ++ suffix27
theorem safe26 : safeChunk chunk26 = true := by decide +kernel
theorem rest26 : verbatimRest suffix26 = ['}', '%'] := by
  rw [suffix26, invariant1_safe_chunk chunk26 suffix27 safe26]
  exact rest27
def suffix25 : List Char := chunk25 ++ suffix26
theorem safe25 : safeChunk chunk25 = true := by decide +kernel
theorem rest25 : verbatimRest suffix25 = ['}', '%'] := by
  rw [suffix25, invariant1_safe_chunk chunk25 suffix26 safe25]
  exact rest26
def suffix24 : List Char := chunk24 ++ suffix25
theorem safe24 : safeChunk chunk24 = true := by decide +kernel
theorem rest24 : verbatimRest suffix24 = ['}', '%'] := by
  rw [suffix24, invariant1_safe_chunk chunk24 suffix25 safe24]
  exact rest25
def suffix23 : List Char := chunk23 ++ suffix24
theorem safe23 : safeChunk chunk23 = true := by decide +kernel
theorem rest23 : verbatimRest suffix23 = ['}', '%'] := by
  rw [suffix23, invariant1_safe_chunk chunk23 suffix24 safe23]
  exact rest24
def suffix22 : List Char := chunk22 ++ suffix23
theorem safe22 : safeChunk chunk22 = true := by decide +kernel
theorem rest22 : verbatimRest suffix22 = ['}', '%'] := by
  rw [suffix22, invariant1_safe_chunk chunk22 suffix23 safe22]
  exact rest23
def suffix21 : List Char := chunk21 ++ suffix22
theorem safe21 : safeChunk chunk21 = true := by decide +kernel
theorem rest21 : verbatimRest suffix21 = ['}', '%'] := by
  rw [suffix21, invariant1_safe_chunk chunk21 suffix22 safe21]
  exact rest22
def suffix20 : List Char := chunk20 ++ suffix21
theorem safe20 : safeChunk chunk20 = true := by decide +kernel
theorem rest20 : verbatimRest suffix20 = ['}', '%'] := by
  rw [suffix20, invariant1_safe_chunk chunk20 suffix21 safe20]
  exact rest21
def suffix19 : List Char := chunk19 ++ suffix20
theorem safe19 : safeChunk chunk19 = true := by decide +kernel
theorem rest19 : verbatimRest suffix19 = ['}', '%'] := by
  rw [suffix19, invariant1_safe_chunk chunk19 suffix20 safe19]
  exact rest20
def suffix18 : List Char := chunk18 ++ suffix19
theorem safe18 : safeChunk chunk18 = true := by decide +kernel
theorem rest18 : verbatimRest suffix18 = ['}', '%'] := by
  rw [suffix18, invariant1_safe_chunk chunk18 suffix19 safe18]
  exact rest19
def suffix17 : List Char := chunk17 ++ suffix18
theorem safe17 : safeChunk chunk17 = true := by decide +kernel
theorem rest17 : verbatimRest suffix17 = ['}', '%'] := by
  rw [suffix17, invariant1_safe_chunk chunk17 suffix18 safe17]
  exact rest18
def suffix16 : List Char := chunk16 ++ suffix17
theorem safe16 : safeChunk chunk16 = true := by decide +kernel
theorem rest16 : verbatimRest suffix16 = ['}', '%'] := by
  rw [suffix16, invariant1_safe_chunk chunk16 suffix17 safe16]
  exact rest17
def suffix15 : List Char := chunk15 ++ suffix16
theorem safe15 : safeChunk chunk15 = true := by decide +kernel
theorem rest15 : verbatimRest suffix15 = ['}', '%'] := by
  rw [suffix15, invariant1_safe_chunk chunk15 suffix16 safe15]
  exact rest16
def suffix14 : List Char := chunk14 ++ suffix15
theorem safe14 : safeChunk chunk14 = true := by decide +kernel
theorem rest14 : verbatimRest suffix14 = ['}', '%'] := by
  rw [suffix14, invariant1_safe_chunk chunk14 suffix15 safe14]
  exact rest15
def suffix13 : List Char := chunk13 ++ suffix14
theorem safe13 : safeChunk chunk13 = true := by decide +kernel
theorem rest13 : verbatimRest suffix13 = ['}', '%'] := by
  rw [suffix13, invariant1_safe_chunk chunk13 suffix14 safe13]
  exact rest14
def suffix12 : List Char := chunk12 ++ suffix13
theorem safe12 : safeChunk chunk12 = true := by decide +kernel
theorem rest12 : verbatimRest suffix12 = ['}', '%'] := by
  rw [suffix12, invariant1_safe_chunk chunk12 suffix13 safe12]
  exact rest13
def suffix11 : List Char := chunk11 ++ suffix12
theorem safe11 : safeChunk chunk11 = true := by decide +kernel
theorem rest11 : verbatimRest suffix11 = ['}', '%'] := by
  rw [suffix11, invariant1_safe_chunk chunk11 suffix12 safe11]
  exact rest12
def suffix10 : List Char := chunk10 ++ suffix11
theorem safe10 : safeChunk chunk10 = true := by decide +kernel
theorem rest10 : verbatimRest suffix10 = ['}', '%'] := by
  rw [suffix10, invariant1_safe_chunk chunk10 suffix11 safe10]
  exact rest11
def suffix9 : List Char := chunk9 ++ suffix10
theorem safe9 : safeChunk chunk9 = true := by decide +kernel
theorem rest9 : verbatimRest suffix9 = ['}', '%'] := by
  rw [suffix9, invariant1_safe_chunk chunk9 suffix10 safe9]
  exact rest10
def suffix8 : List Char := chunk8 ++ suffix9
theorem safe8 : safeChunk chunk8 = true := by decide +kernel
theorem rest8 : verbatimRest suffix8 = ['}', '%'] := by
  rw [suffix8, invariant1_safe_chunk chunk8 suffix9 safe8]
  exact rest9
def suffix7 : List Char := chunk7 ++ suffix8
theorem safe7 : safeChunk chunk7 = true := by decide +kernel
theorem rest7 : verbatimRest suffix7 = ['}', '%'] := by
  rw [suffix7, invariant1_safe_chunk chunk7 suffix8 safe7]
  exact rest8
def suffix6 : List Char := chunk6 ++ suffix7
theorem safe6 : safeChunk chunk6 = true := by decide +kernel
theorem rest6 : verbatimRest suffix6 = ['}', '%'] := by
  rw [suffix6, invariant1_safe_chunk chunk6 suffix7 safe6]
  exact rest7
def suffix5 : List Char := chunk5 ++ suffix6
theorem safe5 : safeChunk chunk5 = true := by decide +kernel
theorem rest5 : verbatimRest suffix5 = ['}', '%'] := by
  rw [suffix5, invariant1_safe_chunk chunk5 suffix6 safe5]
  exact rest6
def suffix4 : List Char := chunk4 ++ suffix5
theorem safe4 : safeChunk chunk4 = true := by decide +kernel
theorem rest4 : verbatimRest suffix4 = ['}', '%'] := by
  rw [suffix4, invariant1_safe_chunk chunk4 suffix5 safe4]
  exact rest5
def suffix3 : List Char := chunk3 ++ suffix4
theorem safe3 : safeChunk chunk3 = true := by decide +kernel
theorem rest3 : verbatimRest suffix3 = ['}', '%'] := by
  rw [suffix3, invariant1_safe_chunk chunk3 suffix4 safe3]
  exact rest4
def suffix2 : List Char := chunk2 ++ suffix3
theorem safe2 : safeChunk chunk2 = true := by decide +kernel
theorem rest2 : verbatimRest suffix2 = ['}', '%'] := by
  rw [suffix2, invariant1_safe_chunk chunk2 suffix3 safe2]
  exact rest3
def suffix1 : List Char := chunk1 ++ suffix2
theorem safe1 : safeChunk chunk1 = true := by decide +kernel
theorem rest1 : verbatimRest suffix1 = ['}', '%'] := by
  rw [suffix1, invariant1_safe_chunk chunk1 suffix2 safe1]
  exact rest2
def suffix0 : List Char := chunk0 ++ suffix1
theorem safe0 : safeChunk chunk0 = true := by decide +kernel
theorem rest0 : verbatimRest suffix0 = ['}', '%'] := by
  rw [suffix0, invariant1_safe_chunk chunk0 suffix1 safe0]
  exact rest1
#print axioms rest0
end PegHs.MetaExecution.Verbatim47Data
