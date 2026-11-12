-- Recognition projection of the generated strict File rule. Child calls, memo
-- hits, and runtime combinators retain their separate semantic obligations.
module Main (main) where

import Control.Monad (forM_, guard)
import Data.Char (isDigit, isSpace, ord)
import Data.List (intercalate, tails)
import System.Environment (getArgs)
import System.Exit (die)
import Text.ParserCombinators.ReadP

token :: String -> ReadP ()
token s = skipSpaces >> string s >> pure ()

quoted :: ReadP String
quoted = skipSpaces >> readS_to_P reads

leanString :: String -> String
leanString s = "(String.ofList [" ++ intercalate ", " ["Char.ofNat " ++ show (ord c) | c <- s] ++ "])"

-- Call sites are numbered by occurrence; targets are resolved against the
-- rule names accepted here. The independent metagrammar extraction checks IDs.
call :: Int -> ReadP String
call site = do
  token "peg'rule'"
  target <- choice [string name >> pure number | (name, number) <-
    [("TopItem","1"), ("TopOne","2"), ("Here","3"), ("Ws","4"), ("SpaceChar","5"),
     ("Comment","6"), ("InlineSp","7"), ("Ident","8"), ("IdentStart","9"), ("IdentChar","10"), ("Verbatim","11"), ("Directive","12"), ("Declaration","13"),
     ("TemplateParams","14"), ("TemplateParam","15"), ("TypeText","16"),
     ("ParamList","17"), ("ParamChunks","18"), ("ParamChunk","19"), ("Alts","20"),
     ("MoreAlt","21"), ("Alt","22"), ("Constructor","23"), ("Item","24"), ("DeclStart","25"), ("Binding","26"), ("PrefixE","27"), ("Labeled","28"), ("LabelPart","29"), ("SuffixE","30"), ("PostOps","31"), ("PostOp","32"), ("Primary","33"), ("PredCode","47"), ("Action","46"), ("Escape","41"), ("EscapeBody","42"), ("ArgCode","51"), ("HsParen","53")]]
  pure ("(.call " ++ show site ++ " " ++ target ++ ")")

production :: ReadP String
production = do
  mapM_ token ["peg'rule'File", "=", "PegRt.memo", "peg'memo'File", "\"File\"",
    "(", "PegRt.choice", "[", "do", "{", "_", "<-"]
  ws <- call 0
  mapM_ token [";", "peg'v0", "<-", "PegRt.many", "("]
  item <- call 1
  mapM_ token [")", ";", "PegRt.labeledMessage"]
  label <- quoted
  message <- quoted
  mapM_ token ["PegPrelude.Nothing", "(", "PegRt.choice", "[", "do", "{",
    "PegRt.notP", "(", "PegRt.anyChar", ")", ";", "PegPrelude.pure", "(", ")",
    "}", "]", ")", ";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  pure (".seq " ++ ws ++ " (.seq (.star " ++ item ++ ") (.label " ++
    leanString label ++ " (some " ++ leanString message ++ ") (.notAhead (.terminal 0))))")

header :: String -> ReadP ()
header name = mapM_ token ["peg'rule'" ++ name, "=", "PegRt.memo", "peg'memo'" ++ name,
  show name, "(", "PegRt.choice", "["]

topItem :: ReadP String
topItem = do
  header "TopItem"
  mapM_ token ["do", "{", "peg'v0", "<-"]
  item <- call 2
  mapM_ token [";", "_", "<-"]
  ws <- call 3
  mapM_ token [";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  pure (".seq " ++ item ++ " " ++ ws)

topOne :: ReadP String
topOne = do
  header "TopOne"
  let branch site binder = do
        mapM_ token ["do", "{", binder, "<-"]
        value <- call site
        mapM_ token [";", "PegPrelude.pure", binder, "}"]
        pure value
  first <- branch 4 "peg'v0"
  token ","
  second <- branch 5 "peg'v1"
  token ","
  third <- branch 6 "peg'v2"
  mapM_ token ["]", ")"]
  pure (".alt " ++ first ++ " (.alt " ++ second ++ " " ++ third ++ ")")

whitespace :: ReadP String
whitespace = do
  header "Ws"
  mapM_ token ["do", "{", "_", "<-", "PegRt.skipMany", "(", "PegRt.choice", "["]
  let ignored site = do
        mapM_ token ["do", "{", "_", "<-"]
        value <- call site
        mapM_ token [";", "PegPrelude.pure", "()", "}"]
        pure value
  space <- ignored 7
  token ","
  comment <- ignored 8
  mapM_ token ["]", ")", ";", "PegPrelude.pure", "()", "}", "]", ")"]
  pure (".star (.alt " ++ space ++ " " ++ comment ++ ")")

-- Only the generated LINE and COLUMN pragmas may surround embedded expressions.
pragma :: String -> ReadP ()
pragma name = do
  mapM_ token ["{-#", name]
  skipSpaces
  _ <- munch1 isDigit
  if name == "LINE" then quoted >> pure () else pure ()
  token "#-}"

embedded :: [String] -> ReadP ()
embedded expr = pragma "LINE" >> pragma "COLUMN" >> mapM_ token expr >> pragma "LINE"

filteredChar :: String -> String -> Int -> Int -> ReadP String
filteredChar name predicate site terminal = do
  header name
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "c", "<-",
    "PegRt.capture", "(", "PegRt.anyChar", ")", ";", "PegRt.predicate", "(", "\\_col", "->"]
  embedded [predicate, "(", "firstChar", "c", ")"]
  mapM_ token [")", ";", "_span", "<-", "PegRt.spanFrom", "peg'start", ";", "PegPrelude.pure", "("]
  embedded ["()"]
  mapM_ token [")", "}", "]", ")"]
  pure (".seq (.bind " ++ show site ++ " \"c\" (.capture (.terminal " ++ show terminal ++
    "))) (.predicate " ++ show site ++ ")")

inlineSpace :: ReadP String
inlineSpace = do
  header "InlineSp"
  mapM_ token ["do", "{", "PegRt.skipMany", "(", "PegRt.cls"]
  ranges <- skipSpaces >> readS_to_P reads
  guard (ranges == [(' ', ' '), ('\t', '\t')])
  _ <- quoted
  mapM_ token [")", ";", "PegPrelude.pure", "()", "}", "]", ")"]
  pure ".star (.terminal 5)"

identifier :: ReadP String
identifier = do
  header "Ident"
  mapM_ token ["do", "{", "peg'v0", "<-", "PegRt.capture", "(", "PegRt.choice", "[",
    "do", "{", "_", "<-"]
  initial <- call 9
  mapM_ token [";", "_", "<-", "PegRt.skipMany", "("]
  following <- call 10
  mapM_ token [")", ";", "PegPrelude.pure", "()", "}", "]", ")", ";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  pure (".capture (.seq " ++ initial ++ " (.star " ++ following ++ "))")

literal :: String -> ReadP ()
literal expected = do
  token "PegRt.lit"
  value <- quoted
  guard (value == expected)
  _ <- quoted -- expected-token text does not affect recognition
  pure ()

positionRule :: ReadP String
positionRule = do
  header "Here"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";",
    "_span", "<-", "PegRt.spanFrom", "peg'start", ";", "PegPrelude.pure", "("]
  embedded ["here", "_span"]
  mapM_ token [")", "}", "]", ")"]
  pure ".eps"

verbatimRule :: ReadP String
verbatimRule = do
  header "Verbatim"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";"]
  literal "%{"
  mapM_ token [";", "l", "<-"]
  here <- call 11
  mapM_ token [";", "b", "<-", "PegRt.capture", "(", "PegRt.skipMany", "(",
    "PegRt.choice", "[", "do", "{", "PegRt.notP", "("]
  literal "}%"
  mapM_ token [")", ";", "PegRt.anyChar", ";", "PegPrelude.pure", "()", "}", "]", ")", ")",
    ";", "PegRt.choice", "[", "do", "{", "PegRt.labeledMessage"]
  name <- quoted
  message <- quoted
  mapM_ token ["PegPrelude.Nothing", "("]
  literal "}%"
  mapM_ token [")", ";", "PegPrelude.pure", "()", "}", "]", ";", "_span", "<-",
    "PegRt.spanFrom", "peg'start", ";", "PegPrelude.pure", "("]
  embedded ["uncurry", "TVerbatim", "(", "verbatimBody", "l", "b", ")"]
  mapM_ token [")", "}", "]", ")"]
  pure (".seq (.terminal 8) (.seq (.bind 3 \"l\" " ++ here ++
    ") (.seq (.bind 4 \"b\" (.capture (.star (.seq (.notAhead (.terminal 9)) (.terminal 10))))) " ++
    "(.label " ++ leanString name ++ " (some " ++ leanString message ++ ") (.terminal 11))))")

directiveRule :: ReadP String
directiveRule = do
  header "Directive"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "l", "<-"]
  loc <- call 12
  token ";"
  literal "%"
  mapM_ token [";", "n", "<-", "PegRt.choice", "[", "do", "{", "peg'v0", "<-", "PegRt.labeledMessage"]
  label <- quoted
  message <- quoted
  mapM_ token ["PegPrelude.Nothing", "("]
  name <- call 13
  mapM_ token [")", ";", "PegPrelude.pure", "peg'v0", "}", "]", ";", "_", "<-"]
  space <- call 14
  mapM_ token [";", "al", "<-"]
  argLoc <- call 15
  mapM_ token [";", "raw", "<-", "PegRt.capture", "(", "PegRt.skipMany", "(",
    "PegRt.choice", "[", "do", "{", "PegRt.notP", "("]
  literal "\n"
  mapM_ token [")", ";", "PegRt.anyChar", ";", "PegPrelude.pure", "()", "}", "]", ")", ")",
    ";", "_span", "<-", "PegRt.spanFrom", "peg'start", ";", "PegPrelude.pure", "("]
  embedded ["TDirective", "l", "n", "al", "(", "directiveArg", "n", "raw", ")"]
  mapM_ token [")", "}", "]", ")"]
  let body = ".bind 8 \"raw\" (.capture (.star (.seq (.notAhead (.terminal 13)) (.terminal 14))))"
      labelled = "(.label " ++ leanString label ++ " (some " ++ leanString message ++ ") " ++ name ++ ")"
  pure (".seq (.bind 5 \"l\" " ++ loc ++ ") (.seq (.terminal 12) (.seq (.bind 6 \"n\" " ++ labelled ++
    ") (.seq " ++ space ++ " (.seq (.bind 7 \"al\" " ++ argLoc ++ ") (" ++ body ++ ")))))")

declarationRule :: ReadP String
declarationRule = do
  header "Declaration"
  annotation <- do
    start
    loc <- named 9 "l" 16
    name <- named 10 "n" 17
    templates <- opt 11 "tps" 18
    params <- opt 12 "ps" 19
    ws <- ignored 20
    token ";"
    literal "::"
    spaces <- ignored 21
    typeLoc <- named 13 "tl" 22
    mapM_ token [";", "ty", "<-", "PegRt.choice", "[", "do", "{", "peg'v0", "<-"]
    ty <- labelled (call 23)
    mapM_ token [";", "PegPrelude.pure", "peg'v0", "}", "]"]
    endAction ["TAnnot", "l", "n", "(", "maybe", "[]", "id", "ps", ")", "(", "maybe", "[]", "id", "tps", ")", "(", "Located", "tl", "ty", ")"]
    pure (sequenceBody [loc, name, templates, params, ws, "(.terminal 15)", spaces, typeLoc, bind 14 "ty" ty])
  token ","
  definition <- do
    start
    loc <- named 15 "l" 24
    name <- named 16 "n" 25
    templates <- opt 17 "tps" 26
    ws <- ignored 27
    token ";"
    literal "<-"
    alts <- named 18 "as" 28
    endAction ["TDef", "l", "n", "(", "maybe", "[]", "(", "map", "templateParamName", ")", "tps", ")", "as"]
    pure (sequenceBody [loc, name, templates, ws, "(.terminal 16)", alts])
  token ","
  start
  name <- ignored 29
  templates <- skipOpt 30
  params <- skipOpt 31
  ws <- ignored 32
  token ";"
  paramGuard <- labelled $ do
    mapM_ token ["PegRt.choice", "[", "do", "{", "PegRt.notP", "("]
    literal "<-"
    mapM_ token [")", ";", "PegPrelude.pure", "()", "}", "]"]
    pure "(.notAhead (.terminal 17))"
  mapM_ token [";", "PegRt.choice", "[", "do", "{"]
  delim <- labelled $ do
    mapM_ token ["PegRt.choice", "[", "do", "{"]
    literal "::"
    mapM_ token [";", "PegPrelude.pure", "()", "}", ",", "do", "{"]
    literal "<-"
    mapM_ token [";", "PegPrelude.pure", "()", "}", "]"]
    pure "(.alt (.terminal 18) (.terminal 19))"
  mapM_ token [";", "PegPrelude.pure", "()", "}", "]"]
  endAction ["TVerbatim", "(", "Loc", "0", "0", "0", ")", "T.empty"]
  mapM_ token ["]", ")"]
  let fallback = sequenceBody [name, templates, params, ws, paramGuard, delim]
  pure (".alt " ++ annotation ++ " (.alt " ++ definition ++ " " ++ fallback ++ ")")
  where
    start = mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset"]
    bind :: Int -> String -> String -> String
    bind i n body = "(.bind " ++ show i ++ " " ++ show n ++ " " ++ body ++ ")"
    named i n site = mapM_ token [";", n, "<-"] >> bind i n <$> call site
    ignored site = mapM_ token [";", "_", "<-"] >> call site
    optionalCall site = token "(" *> call site <* token ")"
    opt i n site = do
      mapM_ token [";", n, "<-", "PegRt.optional"]
      body <- optionalCall site
      pure ("(.alt " ++ bind i n body ++ " .eps)")
    skipOpt site = do
      mapM_ token [";", "_", "<-", "PegRt.skipOptional"]
      body <- optionalCall site
      pure ("(.alt " ++ body ++ " .eps)")


labelled :: ReadP String -> ReadP String
labelled body = do
  token "PegRt.labeledMessage"
  name <- quoted
  message <- quoted
  token "PegPrelude.Nothing"
  child <- token "(" *> body <* token ")"
  pure ("(.label " ++ leanString name ++ " (some " ++ leanString message ++ ") " ++ child ++ ")")

sequenceBody :: [String] -> String
sequenceBody = foldr1 (\x y -> "(.seq " ++ x ++ " " ++ y ++ ")")

-- Both argument forms put whitespace on either side of a literal separator.
separatedArgument :: Int -> String -> Int -> ReadP String
separatedArgument firstSite separator terminal = do
  mapM_ token ["(", "PegRt.choice", "[", "do", "{", "_", "<-"]
  before <- call firstSite
  token ";"
  literal separator
  mapM_ token [";", "_", "<-"]
  after <- call (firstSite + 1)
  mapM_ token [";", "peg'v0", "<-"]
  value <- call (firstSite + 2)
  mapM_ token [";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  pure ("(.seq " ++ before ++ " (.seq (.terminal " ++ show terminal ++ ") (.seq " ++ after ++ " " ++ value ++ ")))")

endAction :: [String] -> ReadP ()
endAction expr = do
  mapM_ token [";", "_span", "<-", "PegRt.spanFrom", "peg'start", ";", "PegPrelude.pure", "("]
  embedded expr
  mapM_ token [")", "}"]

returnAction :: [String] -> ReadP ()
returnAction expr = endAction expr >> mapM_ token ["]", ")"]

templateParamsRule :: ReadP String
templateParamsRule = do
  header "TemplateParams"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";"]
  literal "<"
  mapM_ token [";", "_", "<-"]
  ws <- call 33
  mapM_ token [";", "p", "<-"]
  first <- call 34
  mapM_ token [";", "ps", "<-", "PegRt.many"]
  rest <- separatedArgument 35 "," 21
  mapM_ token [";", "_", "<-"]
  endWs <- call 38
  token ";"
  literal ">"
  returnAction ["p", ":", "ps"]
  pure (".seq (.terminal 20) (.seq " ++ ws ++ " (.seq (.bind 19 \"p\" " ++ first ++
    ") (.seq (.bind 20 \"ps\" (.star " ++ rest ++ ")) (.seq " ++ endWs ++ " (.terminal 22)))))")

templateParamRule :: ReadP String
templateParamRule = do
  header "TemplateParam"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "n", "<-"]
  name <- call 39
  mapM_ token [";", "ty", "<-", "PegRt.optional"]
  annotation <- separatedArgument 40 "::" 23
  returnAction ["TemplateParam", "n", "ty"]
  pure (".seq (.bind 21 \"n\" " ++ name ++ ") (.alt (.bind 22 \"ty\" " ++ annotation ++ ") .eps)")

paramChunkRule :: ReadP String
paramChunkRule = do
  header "ParamChunk"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "_", "<-"]
  ws <- call 47
  mapM_ token [";", "l", "<-"]
  loc <- call 48
  mapM_ token [";", "c", "<-", "PegRt.capture", "("]
  code <- call 49
  token ")"
  nonempty <- predicate 4 ["not", "(", "T.null", "(", "T.strip", "c", ")", ")"]
  form <- predicate 5 ["paramError", "l", "c", "/=", "Just", "paramFormMessage"]
  ty <- predicate 6 ["paramError", "l", "c", "==", "Nothing"]
  mapM_ token [";", "PegRt.labeled"]
  delimiterLabel <- quoted
  mapM_ token ["PegPrelude.Nothing", "(", "PegRt.choice", "[", "do", "{", "PegRt.andP", "(", "PegRt.cls"]
  ranges <- skipSpaces >> readS_to_P reads
  guard (ranges == [(',', ','), (')', ')')])
  _ <- quoted
  mapM_ token [")", ";", "PegPrelude.pure", "()", "}", "]", ")"]
  returnAction ["param", "l", "c"]
  let delimiter = "(.label " ++ leanString delimiterLabel ++ " none (.ahead (.terminal 29)))"
  pure (sequenceBody [ws, "(.bind 27 \"l\" " ++ loc ++ ")", "(.bind 28 \"c\" (.capture " ++ code ++ "))",
    nonempty, form, ty, delimiter])
  where
    predicate :: Int -> [String] -> ReadP String
    predicate site expr = token ";" >> labelled (do
      mapM_ token ["PegRt.choice", "[", "do", "{", "PegRt.predicate", "(", "\\_col", "->"]
      embedded expr
      mapM_ token [")", ";", "PegPrelude.pure", "()", "}", "]"]
      pure ("(.predicate " ++ show site ++ ")"))

paramChunksRule :: ReadP String
paramChunksRule = do
  header "ParamChunks"
  let chunk site = do
        mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "p", "<-"]
        call site
  first <- chunk 44
  token ";"
  literal ","
  mapM_ token [";", "rest", "<-"]
  rest <- call 45
  endAction ["p", ":", "rest"]
  token ","
  lastChunk <- chunk 46
  token ";"
  literal ")"
  returnAction ["[", "p", "]"]
  pure (".alt (.seq (.bind 24 \"p\" " ++ first ++ ") (.seq (.terminal 27) (.bind 25 \"rest\" " ++
    rest ++ "))) (.seq (.bind 26 \"p\" " ++ lastChunk ++ ") (.terminal 28))")

declStartRule :: ReadP String
declStartRule = do
  header "DeclStart"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "_", "<-"]
  name <- call 72
  templates <- optional 73
  params <- optional 74
  mapM_ token [";", "_", "<-"]
  ws <- call 75
  mapM_ token [";", "PegRt.choice", "[", "do", "{"]
  literal "::"
  mapM_ token [";", "PegPrelude.pure", "()", "}", ",", "do", "{"]
  literal "<-"
  mapM_ token [";", "PegPrelude.pure", "()", "}", "]"]
  returnAction ["()"]
  pure (sequenceBody [name, templates, params, ws, "(.alt (.terminal 32) (.terminal 33))"])
  where
    optional site = do
      mapM_ token [";", "_", "<-", "PegRt.skipOptional", "("]
      child <- call site
      token ")"
      pure ("(.alt " ++ child ++ " .eps)")

bindingRule :: ReadP String
bindingRule = do
  header "Binding"
  mapM_ token ["do", "{", "peg'v0", "<-"]
  name <- call 76
  token ";"
  literal ":"
  mapM_ token [";", "PegRt.notP", "("]
  literal ":"
  mapM_ token [")", ";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  pure (sequenceBody [name, "(.terminal 34)", "(.notAhead (.terminal 35))"])

depthCall :: Int -> [String] -> ReadP String
depthCall site argument = do
  mapM_ token ["PegRt.withCol", "(", "\\_col", "->"]
  child <- call site
  token "("
  embedded argument
  mapM_ token [")", ")"]
  pure child

depthHeader :: String -> ReadP ()
depthHeader name = mapM_ token ["peg'rule'" ++ name, "d", "=", "PegRt.memoArg",
  "peg'memo'" ++ name, show name, "d", "(", "PegRt.choice", "["]

quotedLiteralRule :: String -> Char -> Int -> Int -> ReadP String
quotedLiteralRule name delimiter site firstTerminal = do
  header name
  mapM_ token ["do", "{"]
  literal [delimiter]
  mapM_ token [";", "PegRt.skipMany", "(", "PegRt.choice", "[", "do", "{", "_", "<-"]
  escape <- call site
  mapM_ token [";", "PegPrelude.pure", "()", "}", ",", "do", "{", "PegRt.notP", "(", "PegRt.cls"]
  ranges <- skipSpaces >> readS_to_P reads
  guard (ranges == [(delimiter, delimiter), ('\\', '\\'), ('\n', '\n')])
  _ <- quoted
  mapM_ token [")", ";", "PegRt.anyChar", ";", "PegPrelude.pure", "()", "}", "]", ")",
    ";", "PegRt.choice", "[", "do", "{"]
  closing <- labelled (literal [delimiter] >> pure (term 3))
  mapM_ token [";", "PegPrelude.pure", "()", "}", "]", ";", "PegPrelude.pure", "()", "}", "]", ")"]
  let plain = sequenceBody ["(.notAhead " ++ term 1 ++ ")", term 2]
  pure (sequenceBody [term 0, "(.star (.alt " ++ escape ++ " " ++ plain ++ "))", closing])
  where term offset = "(.terminal " ++ show (firstTerminal + offset) ++ ")"

escapeRule :: ReadP String
escapeRule = do
  header "Escape"
  mapM_ token ["do", "{"]
  literal "\\"
  mapM_ token [";", "_", "<-", "PegRt.choice", "[", "do", "{", "_", "<-", "PegRt.labeled"]
  name <- quoted
  mapM_ token ["PegPrelude.Nothing", "("]
  body <- call 138
  mapM_ token [")", ";", "PegPrelude.pure", "()", "}", "]", ";", "PegPrelude.pure", "()", "}", "]", ")"]
  pure (".seq (.terminal 75) (.label " ++ leanString name ++ " none " ++ body ++ ")")

suffixRule :: ReadP String
suffixRule = do
  depthHeader "SuffixE"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "p", "<-"]
  atom <- depthCall 99 ["d"]
  mapM_ token [";", "ops", "<-"]
  ops <- depthCall 100 ["d", "+", "snd", "p"]
  returnAction ["(", "foldl", "applyOp", "(", "fst", "p", ")", "ops", ",", "snd", "p", "+", "length", "ops", ")"]
  pure (".action 8 (.seq (.bind 51 \"p\" " ++ atom ++ ") (.bind 52 \"ops\" " ++ ops ++ "))")

postOpsRule :: ReadP String
postOpsRule = do
  depthHeader "PostOps"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "c", "<-"]
  op <- depthCall 101 ["d"]
  mapM_ token [";", "cs", "<-"]
  rest <- depthCall 102 ["d", "+", "1"]
  endAction ["c", ":", "cs"]
  mapM_ token [",", "do", "{", "peg'start", "<-", "PegRt.getOffset"]
  returnAction ["[]"]
  pure (".alt (.action 9 (.seq (.bind 53 \"c\" " ++ op ++ ") (.bind 54 \"cs\" " ++ rest ++ "))) (.action 10 .eps)")

postOpRule :: ReadP String
postOpRule = do
  depthHeader "PostOp"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "_", "<-"]
  ws <- call 103
  mapM_ token [";", "PegRt.andP", "("]
  operators
  mapM_ token [")", ";"]
  limit <- depthCheck 11
  mapM_ token [";", "c", "<-", "PegRt.capture", "("]
  operators
  token ")"
  returnAction ["firstChar", "c"]
  pure (".action 11 " ++ sequenceBody [ws, "(.ahead (.terminal 52))", limit,
    "(.bind 55 \"c\" (.capture (.terminal 53)))"])
  where
    operators = do
      token "PegRt.cls"
      ranges <- skipSpaces >> readS_to_P reads
      guard (ranges == [('*', '*'), ('+', '+'), ('?', '?')])
      quoted >> pure ()

labeledRule :: ReadP String
labeledRule = do
  depthHeader "Labeled"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "e", "<-"]
  expr <- depthCall 94 ["d"]
  mapM_ token [";", "lab", "<-", "PegRt.optional", "("]
  suffix <- depthCall 95 ["d", "+", "snd", "e"]
  token ")"
  returnAction ["maybe", "e", "(", "\\", "(", "l", ",", "n", ")", "->", "deeper", "(", "\\x",
    "->", "ELabel", "l", "x", "n", ")", "e", ")", "lab"]
  pure (".action 7 (.seq (.bind 47 \"e\" " ++ expr ++ ") (.alt (.bind 48 \"lab\" " ++ suffix ++ ") .eps))")

depthCheck :: Int -> ReadP String
depthCheck site = labelled $ do
  mapM_ token ["PegRt.choice", "[", "do", "{", "PegRt.predicate", "(", "\\_col", "->"]
  embedded ["d", "<", "maxDepth"]
  mapM_ token [")", ";", "PegPrelude.pure", "()", "}", "]"]
  pure ("(.predicate " ++ show site ++ ")")

labelPartRule :: ReadP String
labelPartRule = do
  depthHeader "LabelPart"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "_", "<-"]
  ws <- call 96
  mapM_ token [";", "l", "<-"]
  loc <- call 97
  mapM_ token [";", "PegRt.andP", "("]
  literal "^"
  mapM_ token [")", ";"]
  limit <- depthCheck 10
  token ";" >> literal "^"
  mapM_ token [";", "n", "<-"]
  name <- call 98
  returnAction ["(", "l", ",", "n", ")"]
  pure (sequenceBody [ws, "(.bind 49 \"l\" " ++ loc ++ ")", "(.ahead (.terminal 50))", limit,
    "(.terminal 51)", "(.bind 50 \"n\" " ++ name ++ ")"])

prefixRule :: ReadP String
prefixRule = do
  depthHeader "PrefixE"
  positive <- operator "&" "EAnd" 0 77 36
  token ","
  positivePred <- semantic "&" "True" 3 81 40 43
  token ","
  negative <- operator "!" "ENot" 1 84 42
  token ","
  negativePred <- semantic "!" "False" 5 88 46 45
  token ","
  capture <- operator "$" "ECapture" 2 91 48
  mapM_ token [",", "do", "{", "peg'v3", "<-"]
  child <- depthCall 93 ["d"]
  mapM_ token [";", "PegPrelude.pure", "peg'v3", "}", "]", ")"]
  pure (foldr1 (\x y -> "(.alt " ++ x ++ " " ++ y ++ ")")
    [positive, positivePred, negative, negativePred, capture, child])
  where
    begin site = mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "_", "<-"] *> call site
    term i = "(.terminal " ++ show (i :: Int) ++ ")"
    action i xs = "(.action " ++ show (i :: Int) ++ " " ++ sequenceBody xs ++ ")"
    bound i name body = "(.bind " ++ show (i :: Int) ++ " " ++ show name ++ " " ++ body ++ ")"
    semantic op truth act site t binder = do
      ws <- begin site
      token ";" >> literal op
      mapM_ token [";", "_", "<-"]
      inner <- call (site + 1)
      token ";" >> literal "{"
      mapM_ token [";", "c", "<-"]
      code <- call (site + 2)
      endAction ["(", "EPred", truth, "c", ",", "0", ")"]
      pure (action act [ws, term t, inner, term (t+1), bound binder "c" code])
    operator op con index site t = do
      ws <- begin site
      mapM_ token [";", "PegRt.andP", "("]
      literal op
      token ")"
      (guardParts, nextSite, nextTerm) <- if op == "$" then pure ([], site+1, t+1) else do
        mapM_ token [";", "PegRt.notP", "(", "PegRt.choice", "[", "do", "{"]
        literal op
        mapM_ token [";", "_", "<-"]
        inner <- call (site+1)
        token ";" >> literal "{"
        mapM_ token [";", "PegPrelude.pure", "()", "}", "]", ")"]
        pure (["(.notAhead " ++ sequenceBody [term (t+1), inner, term (t+2)] ++ ")"], site+2, t+3)
      token ";"
      limit <- depthCheck (7+index)
      token ";" >> literal op
      (spaces, childSite) <- if op == "$" then pure ([], nextSite) else do
        mapM_ token [";", "_", "<-"]
        space <- call nextSite
        pure ([space], nextSite+1)
      let variable = "peg'v" ++ show index
      mapM_ token [";", "e", "<-", "PegRt.choice", "[", "do", "{", variable, "<-"]
      child <- labelled (depthCall childSite ["d", "+", "1"])
      mapM_ token [";", "PegPrelude.pure", variable, "}", "]"]
      endAction ["deeper", con, "e"]
      pure (action (2+2*index) ([ws, "(.ahead " ++ term t ++ ")"] ++ guardParts ++
        [limit, term nextTerm] ++ spaces ++ [bound (42+2*index) "e" child]))

itemRule :: ReadP String
itemRule = do
  mapM_ token ["peg'rule'Item", "d", "=", "PegRt.memoArg", "peg'memo'Item", "\"Item\"", "d",
    "(", "PegRt.choice", "["]
  first <- start 63 37
  mapM_ token [";", "b", "<-"]
  binder <- call 66
  mapM_ token [";", "e", "<-", "PegRt.choice", "[", "do", "{", "peg'v0", "<-"]
  expr <- labelled (withDepth 67)
  mapM_ token [";", "PegPrelude.pure", "peg'v0", "}", "]"]
  endAction ["(", "Item", "l", "(", "Just", "b", ")", "(", "fst", "e", ")", ",", "snd", "e", ")"]
  token ","
  second <- start 68 40
  mapM_ token [";", "e", "<-"]
  plain <- withDepth 71
  returnAction ["(", "Item", "l", "Nothing", "(", "fst", "e", ")", ",", "snd", "e", ")"]
  let bound = sequenceBody (first ++ ["(.bind 38 \"b\" " ++ binder ++ ")", "(.bind 39 \"e\" " ++ expr ++ ")"])
      unbound = sequenceBody (second ++ ["(.bind 41 \"e\" " ++ plain ++ ")"])
  pure (".alt (.action 0 " ++ bound ++ ") (.action 1 " ++ unbound ++ ")")
  where
    start :: Int -> Int -> ReadP [String]
    start site locId = do
      mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "_", "<-"]
      ws <- call site
      mapM_ token [";", "PegRt.notP", "("]
      decl <- call (site + 1)
      mapM_ token [")", ";", "l", "<-"]
      loc <- call (site + 2)
      pure [ws, "(.notAhead " ++ decl ++ ")", "(.bind " ++ show locId ++ " \"l\" " ++ loc ++ ")"]
    withDepth site = do
      mapM_ token ["PegRt.withCol", "(", "\\_col", "->"]
      child <- call site
      token "("
      embedded ["d"]
      mapM_ token [")", ")"]
      pure child

altRule :: ReadP String
altRule = do
  header "Alt"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "_", "<-"]
  ws <- call 54
  mapM_ token [";", "l", "<-"]
  loc <- call 55
  mapM_ token [";", "is", "<-", "PegRt.many", "(", "PegRt.withCol", "(", "\\_col", "->"]
  item <- call 56
  token "("
  embedded ["0"]
  mapM_ token [")", ")", ")", ";", "_", "<-"]
  trailing <- call 57
  action <- optional "act" 58
  ctor <- optional "c" 59
  returnAction ["Alt", "l", "(", "map", "fst", "is", ")", "act", "c"]
  pure (sequenceBody [ws, "(.bind 31 \"l\" " ++ loc ++ ")", "(.bind 32 \"is\" (.star " ++ item ++ "))",
    trailing, "(.alt (.bind 33 \"act\" " ++ action ++ ") .eps)", "(.alt (.bind 34 \"c\" " ++ ctor ++ ") .eps)"])
  where
    optional name site = mapM_ token [";", name, "<-", "PegRt.optional", "("] *> call site <* token ")"

constructorRule :: ReadP String
constructorRule = do
  header "Constructor"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "_", "<-"]
  ws <- call 60
  token ";"
  literal "@"
  mapM_ token [";", "l", "<-"]
  loc <- call 61
  mapM_ token [";", "n", "<-", "PegRt.choice", "[", "do", "{", "peg'v0", "<-"]
  name <- labelled (call 62)
  mapM_ token [";", "PegPrelude.pure", "peg'v0", "}", "]"]
  returnAction ["Located", "l", "n"]
  pure (sequenceBody [ws, "(.terminal 31)", "(.bind 35 \"l\" " ++ loc ++ ")", "(.bind 36 \"n\" " ++ name ++ ")"])

altsRule :: ReadP String
altsRule = do
  header "Alts"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "a", "<-"]
  first <- call 50
  mapM_ token [";", "as", "<-", "PegRt.many", "("]
  rest <- call 51
  token ")"
  returnAction ["a", ":", "as"]
  pure (".seq (.bind 29 \"a\" " ++ first ++ ") (.bind 30 \"as\" (.star " ++ rest ++ "))")

moreAltRule :: ReadP String
moreAltRule = do
  header "MoreAlt"
  mapM_ token ["do", "{", "_", "<-"]
  ws <- call 52
  token ";"
  literal "/"
  mapM_ token [";", "peg'v0", "<-"]
  alt <- call 53
  mapM_ token [";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  pure (".seq " ++ ws ++ " (.seq (.terminal 30) " ++ alt ++ ")")

paramListRule :: ReadP String
paramListRule = do
  header "ParamList"
  mapM_ token ["do", "{"]
  literal "("
  mapM_ token [";", "peg'v0", "<-"]
  chunks <- call 43
  mapM_ token [";", "PegPrelude.pure", "peg'v0", "}", "]", ")"]
  pure (".seq (.terminal 26) " ++ chunks)

typeTextRule :: ReadP String
typeTextRule = do
  header "TypeText"
  mapM_ token ["do", "{", "peg'start", "<-", "PegRt.getOffset", ";", "ty", "<-",
    "PegRt.capture", "(", "PegRt.skipMany", "(", "PegRt.choice", "[", "do", "{", "PegRt.notP", "("]
  literal "\n"
  mapM_ token [")", ";", "PegRt.anyChar", ";", "PegPrelude.pure", "()", "}", "]", ")", ")",
    ";", "PegRt.predicate", "(", "\\_col", "->"]
  embedded ["not", "(", "T.null", "(", "T.stripEnd", "ty", ")", ")"]
  mapM_ token [")", ";", "_span", "<-", "PegRt.spanFrom", "peg'start", ";", "PegPrelude.pure", "("]
  embedded ["T.stripEnd", "ty"]
  mapM_ token [")", "}", "]", ")"]
  pure ".seq (.bind 23 \"ty\" (.capture (.star (.seq (.notAhead (.terminal 24)) (.terminal 25))))) (.predicate 3)"

commentRule :: ReadP String
commentRule = do
  header "Comment"
  mapM_ token ["do", "{"]
  literal "#"
  mapM_ token [";", "PegRt.skipMany", "(", "PegRt.choice", "[", "do", "{", "PegRt.notP", "("]
  literal "\n"
  mapM_ token [")", ";", "PegRt.anyChar", ";", "PegPrelude.pure", "()", "}", "]", ")",
    ";", "PegPrelude.pure", "()", "}", "]", ")"]
  pure ".seq (.terminal 2) (.star (.seq (.notAhead (.terminal 3)) (.terminal 4)))"

main :: IO ()
main = do
  [path] <- getArgs
  source <- lines <$> readFile path
  putStrLn "import MetaExecution\nnamespace PegHs.MetaExecution"
  forM_ [("File", production), ("TopItem", topItem), ("TopOne", topOne), ("Ws", whitespace),
         ("SpaceChar", filteredChar "SpaceChar" "isSpace" 0 1), ("Comment", commentRule), ("Ident", identifier),
         ("IdentStart", filteredChar "IdentStart" "isIdentStart" 1 6),
         ("IdentChar", filteredChar "IdentChar" "isIdentChar" 2 7),
         ("InlineSp", inlineSpace), ("Here", positionRule), ("Verbatim", verbatimRule), ("Directive", directiveRule),
         ("Declaration", declarationRule), ("TemplateParams", templateParamsRule), ("TemplateParam", templateParamRule),
         ("TypeText", typeTextRule), ("ParamList", paramListRule), ("ParamChunks", paramChunksRule),
         ("ParamChunk", paramChunkRule),
         ("Alts", altsRule), ("MoreAlt", moreAltRule), ("Alt", altRule), ("Constructor", constructorRule), ("Item", itemRule),
         ("DeclStart", declStartRule), ("Binding", bindingRule), ("PrefixE", prefixRule),
         ("Labeled", labeledRule), ("LabelPart", labelPartRule), ("SuffixE", suffixRule),
         ("PostOps", postOpsRule), ("PostOp", postOpRule),
         ("Lit1", quotedLiteralRule "Lit1" '\'' 136 67), ("Lit2", quotedLiteralRule "Lit2" '"' 137 71),
         ("Escape", escapeRule)] $
    \(name, parser) -> case [unlines (l : takeWhile (not . all isSpace) rest) |
        l : rest <- tails source, l == "peg'rule'" ++ name ++ (if name `elem` ["Item", "PrefixE", "Labeled", "LabelPart", "SuffixE", "PostOps", "PostOp"] then " d =" else " =")] of
      [body] | [(expr, "")] <- readP_to_S (parser <* skipSpaces <* eof) body ->
        putStrLn ("def translatedStrict" ++ name ++ " : EnvironmentEval.Body := " ++ expr)
      _ -> die ("unsupported or missing generated rule " ++ name)
  putStrLn "end PegHs.MetaExecution"
