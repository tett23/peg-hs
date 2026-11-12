{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Turning the top-level items of a grammar file into a t'Grammar'.
--
-- The parser of the notation, generated from @grammar/Peg.hpeg@ (ADR 0027),
-- calls these functions from its actions. They are exposed for that parser,
-- for its variant without labels that the tests of label safety compile
-- (ADR 0029), and for tests of it; the language server also uses
-- 'isIdentChar'. Use "Peg.Grammar.Parser" to read a grammar.
module Peg.Grammar.Assemble
  ( Top (..)
  , assemble
  , toParam
  , isValidIdent
  , isIdentStart
  , isIdentChar
  , advanceLoc
  , verbatimBody
  , directiveArg
  , directiveComment
  , isImportPath
  , isModuleName
  ) where

import Data.Char (chr, digitToInt, isAlpha, isAlphaNum, isAscii, isAsciiUpper, isDigit, isHexDigit, isSpace, isUpper)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar

-- | A top-level item of a grammar file.
data Top
  = -- | Location of the directive, name, location of the argument, argument.
    TDirective Loc Text Loc Text
  | -- | Location of the body and the body.
    TVerbatim Loc Text
  | -- | Location, rule name, parameters, template parameters (ADR 0031), type.
    TAnnot Loc Text [Param] [TemplateParam] (Located Text)
  | -- | Location, rule name, names of the template parameters, alternatives.
    TDef Loc Text [Text] [Alt]
  deriving (Eq, Show)

-- | Whether a character can start an identifier (ADR 0020).
isIdentStart :: Char -> Bool
isIdentStart c = isAlpha c || c == '_'

-- | Whether a character can follow the first one of an identifier.
isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''

-- | Whether a text is an identifier.
isValidIdent :: Text -> Bool
isValidIdent t = case T.uncons t of
  Just (c, rest) -> isIdentStart c && T.all isIdentChar rest
  Nothing -> False

-- | The location after a text that starts at the given location.
advanceLoc :: Loc -> Text -> Loc
advanceLoc = T.foldl' step
  where
    step (Loc f l _) '\n' = Loc f (l + 1) 1
    step (Loc f l c) _ = Loc f l (c + 1)

-- | A parameter @name :: Type@ from an argument chunk.
toParam :: Located Text -> Either Text Param
toParam (Located l t) = case T.breakOn "::" t of
  (n, rest)
    | not (T.null rest)
    , let name = T.strip n
    , isValidIdent name ->
        let afterSep = T.drop 2 rest
            lead = T.takeWhile isSpace afterSep
            tyLoc = advanceLoc l (n <> "::" <> lead)
            ty = T.strip afterSep
         in if T.null ty then Left "expected a parameter type" else Right (Param name (Located tyLoc ty))
  _ -> Left "expected a parameter of the form name :: Type"

-- | The body of a @%{ ... }%@ block that starts at the given location: a
-- leading newline moves the block to the next line, and surrounding
-- whitespace is removed.
verbatimBody :: Loc -> Text -> (Loc, Text)
verbatimBody l body =
  let (start, text) = case T.uncons body of
        Just ('\n', rest) -> (Loc (locFile l) (locLine l + 1) 1, rest)
        _ -> (l, T.stripStart body)
   in (start, T.stripEnd text)

-- | The argument of a directive from the rest of its line, without its
-- comment and the spaces around it ('directiveComment').
directiveArg :: Text -> Text -> Text
directiveArg name raw = T.strip (fst (directiveComment name raw))

-- | The rest of the line of a directive, after the name of the directive
-- given as the first argument, split into the argument and the comment,
-- which starts with @#@ or is empty. A @#@ starts the comment, except in
-- the argument of @%env@, whose type may contain @#@, and inside the
-- string of @%expect@ and @%message@ (ADR 0089). The parser, the
-- formatter and the highlighting split a directive with this function.
directiveComment :: Text -> Text -> (Text, Text)
directiveComment name raw
  | name == "env" = (raw, "")
  | name `elem` stringDirectives = T.splitAt (outside 0 (T.unpack raw)) raw
  | otherwise = T.break (== '#') raw
  where
    -- The number of characters before the comment, outside and inside a
    -- string.
    outside n = \case
      [] -> n
      '#' : _ -> n
      '"' : rest -> inside (n + 1) rest
      _ : rest -> outside (n + 1) rest
    inside n = \case
      [] -> n
      '\\' : _ : rest -> inside (n + 2) rest
      '"' : rest -> outside (n + 1) rest
      _ : rest -> inside (n + 1) rest

-- The directives whose argument ends with a string (ADR 0089).
stringDirectives :: [Text]
stringDirectives = ["expect", "message"]

-- The argument of @%expect@ or @%message@, given the locations of the
-- directive and of the argument: a name and a string, the string decoded at
-- the location of its opening quote.
stringArg :: Text -> Loc -> Located Text -> Either Diagnostic (Located Text, Located Text)
stringArg directive l (Located al a) =
  case (isValidIdent name, T.uncons quoted) of
    (True, Just ('"', body)) -> do
      (decoded, after) <- decodeString strLoc (T.unpack body)
      if not (T.null (T.strip (T.pack after)))
        then Left formError
        else check decoded
    _ -> Left formError
  where
    (name, rest) = T.break isSpace a
    gap = T.takeWhile isSpace rest
    quoted = T.drop (T.length gap) rest
    strLoc = advanceLoc al (name <> gap)
    formError = Diagnostic l ("%" <> directive <> (if directive == "expect" then " expects a rule name and a string" else " expects a label and a string"))
    what = if directive == "expect" then "the description" else "the message"
    check v
      | T.null v = Left (Diagnostic strLoc (what <> " is empty"))
      | T.any (\c -> c < ' ' || c == '\DEL') v = Left (Diagnostic strLoc (what <> " contains a control character"))
      | otherwise = Right (Located al name, Located strLoc v)

-- Decode the inside of a string after its opening quote at a location,
-- with the escapes of a literal of a rule, up to the closing quote. The
-- rest after the closing quote is returned with the value. The errors have
-- the messages of the errors of a literal (Peg.Grammar.Parser).
decodeString :: Loc -> String -> Either Diagnostic (Text, String)
decodeString start = go (next start '"') []
  where
    next l c = advanceLoc l (T.singleton c)
    go l acc = \case
      [] -> Left (Diagnostic l "unterminated literal")
      '"' : rest -> Right (T.pack (reverse acc), rest)
      '\\' : rest -> escape l (next l '\\') acc rest
      c : rest -> go (next l c) (c : acc) rest
    -- At the backslash and after it.
    escape back l acc = \case
      [] -> Left (Diagnostic l "unterminated literal")
      'u' : rest -> unicode back (next l 'u') acc rest
      c : rest -> case lookup c simple of
        Just d -> go (next l c) (d : acc) rest
        Nothing -> Left (Diagnostic l ("unknown escape \\" <> T.singleton c))
    simple = [('n', '\n'), ('t', '\t'), ('r', '\r'), ('\\', '\\'), ('\'', '\''), ('"', '"'), ('[', '['), (']', ']'), ('-', '-')]
    unicode back l acc = \case
      '{' : rest ->
        let (h, rest') = span isHexDigit rest
            l' = advanceLoc (next l '{') (T.pack h)
            n = foldl (\m d -> m * 16 + toInteger (digitToInt d)) 0 h
         in case rest' of
              '}' : more
                | not (null h) && n <= 0x10FFFF -> go (next l' '}') (chr (fromInteger n) : acc) more
                | otherwise -> Left (Diagnostic back "invalid \\u escape")
              _ -> Left (Diagnostic l' "expected '}'")
      _ -> Left (Diagnostic l "expected '{'")

-- | Check the top-level items and build the grammar: the directives and
-- their arguments, the pairing of each rule's type annotation with its
-- definition, and duplicate rules. The values that the generated module
-- has as written must be what they stand for: the value of @%module@ a
-- module name, and the items of @%export@ items of an export list
-- (ADR 0080). The rules themselves are checked by
-- 'Peg.Grammar.Check.check'.
--
-- A file with @%library@ is a library (ADR 0092): it has no @%module@, its
-- 'grammarModule' is empty at the location of @%library@, and it has only
-- comments and rules besides @%library@. The paths of @%import@ must have
-- the form of 'isImportPath', and a path is imported once.
assemble :: [Top] -> Either [Diagnostic] Grammar
assemble items =
  case errors of
    [] -> case moduleName of
      Just m ->
        Right
          Grammar
            { grammarModule = m
            , grammarImports = [Located l (T.unpack a) | (l, _, a) <- imports]
            , grammarLibrary = libraryLoc
            , grammarStart = single "start"
            , grammarEntries = [Located l a | TDirective l "entry" _ a <- items]
            , grammarExports = concat [splitExports al a | TDirective _ "export" al a <- items]
            , grammarEnv = single "env"
            , grammarTabstop = tabstop
            , grammarNoMemo = [Located l a | TDirective l "nomemo" _ a <- items]
            , grammarLanguages = concat [splitExports al a | TDirective _ "language" al a <- items]
            , grammarSyntax = case [l | TDirective l "syntax" _ _ <- items] of
                l : _ -> Just l
                [] -> Nothing
            , grammarTokens = [Located l a | TDirective l "token" _ a <- items]
            , grammarTrivia = [Located l a | TDirective l "trivia" _ a <- items]
            , grammarInline = [Located l a | TDirective l "inline" _ a <- items]
            , grammarRecovers =
                [ (Located al lab, Located al rule)
                | TDirective _ "recover" al a <- items
                , [lab, rule] <- [T.words a]
                ]
            , grammarSafe = [Located l a | TDirective l "safe" _ a <- items]
            , grammarExpects = [x | Right x <- map snd expects]
            , grammarMessages = [x | Right x <- map snd messages]
            , grammarDeriving = case [Located l (splitExports al a) | TDirective l "deriving" al a <- items] of
                d : _ -> Just d
                [] -> Nothing
            , grammarVerbatim = [Located l t | TVerbatim l t <- items]
            , grammarRules = rules
            }
      Nothing -> Left [Diagnostic (Loc 0 1 1) "missing %module directive"]
    es -> Left (sortOn diagLoc es)
  where
    directives = [(l, n, a) | TDirective l n _ a <- items]
    argLocs = [(n, al, a) | TDirective _ n al a <- items]
    -- GHC lexes qualified do as ITdo regardless of QualifiedDo, and
    -- qualified mdo as ITmdo when RecursiveDo is enabled. LANGUAGE flags
    -- take effect in source order, including the deprecated DoRec alias.
    recursiveDoEnabled = foldl stepRecursiveDo False
      [unLoc x | TDirective _ "language" al a <- items, x <- splitExports al a]
    stepRecursiveDo _ "RecursiveDo" = True
    stepRecursiveDo _ "DoRec" = True
    stepRecursiveDo _ "NoRecursiveDo" = False
    stepRecursiveDo _ "NoDoRec" = False
    stepRecursiveDo enabled _ = enabled
    known = ["module", "start", "entry", "export", "env", "tabstop", "nomemo", "language", "syntax", "token", "trivia", "inline", "recover", "safe", "deriving", "expect", "message", "import", "library"]
    -- ADR 0092
    libraryLoc = case [l | (l, "library", _) <- directives] of
      l : _ -> Just l
      [] -> Nothing
    imports = [(l, al, a) | TDirective l "import" al a <- items]
    libraryErrors = case libraryLoc of
      Nothing -> []
      Just ll ->
        [Diagnostic ll "%library and %module cannot be in the same file" | (_, "module", _) <- take 1 [d | d@(_, "module", _) <- directives]]
          ++ [ Diagnostic l ("a library cannot have %" <> n <> "; write it in the grammar that imports the library")
             | (l, n, _) <- directives
             , n `elem` known
             , n `notElem` ["library", "module"]
             ]
          ++ [Diagnostic l "a library cannot have %{ ... }%; write it in the grammar that imports the library" | TVerbatim l _ <- items]
    -- ADR 0089
    stringArgs d = [(l, stringArg d l (Located al a)) | TDirective l d' al a <- items, d' == d, not (T.null a)]
    expects = stringArgs "expect"
    messages = stringArgs "message"
    single n = case [Located l a | (l, n', a) <- directives, n' == n] of
      x : _ -> Just x
      [] -> Nothing
    moduleName = case libraryLoc of
      Just l -> Just (Located l "")
      Nothing -> single "module"
    tabstop = case single "tabstop" of
      Just (Located l a) | T.all isDigit a, not (T.null a) -> Just (Located l (read (T.unpack a)))
      _ -> Nothing
    annots = M.fromListWith (flip (++)) [(n, [(l, ps, tps, ty)]) | TAnnot l n ps tps ty <- items]
    defs = [(l, n, alts) | TDef l n _ alts <- items]
    defTemplateNames = M.fromList [(n, (l, tns)) | TDef l n tns _ <- items]
    defCounts = M.fromListWith (+) [(n, 1 :: Int) | (_, n, _) <- defs]
    -- A rule without a type annotation has type () (ADR 0066).
    rules =
      [ case M.lookup n annots of
          Just ((al, ps, tps, ty) : _) -> Rule n l ps tps ty (Just al) alts
          _ -> Rule n l [] [] (Located l "()") Nothing alts
      | (l, n, alts) <- defs
      ]
    templateNamesOf n = maybe [] snd (M.lookup n defTemplateNames)
    errors =
      [Diagnostic l ("unknown directive %" <> n) | (l, n, _) <- directives, n `notElem` known]
        ++ [ Diagnostic l ("duplicate %" <> n <> " directive")
           | n <- ["module", "start", "env", "tabstop", "syntax", "deriving", "library"]
           , (l, _, _) : _ : _ <- [reverse [d | d@(_, n', _) <- directives, n' == n]]
           ]
        ++ [Diagnostic l ("%" <> n <> " needs an argument") | (l, n, a) <- directives, n `elem` known, n `notElem` ["syntax", "deriving", "library"], T.null a]
        ++ [Diagnostic l ("%" <> n <> " takes no argument") | (l, n, a) <- directives, n `elem` ["syntax", "library"], not (T.null a)]
        -- ADR 0092
        ++ libraryErrors
        ++ [ Diagnostic al "%import expects a path such as lex/Ident.hpeg: parts of ASCII letters, digits, _, - and . separated by /, other than . and .., ending in .hpeg"
           | (_, al, a) <- imports
           , not (T.null a)
           , not (isImportPath a)
           ]
        ++ [ Diagnostic l (a <> " is imported twice")
           | (k, (l, _, a)) <- zip [0 :: Int ..] imports
           , isImportPath a
           , a `elem` [b | (_, _, b) <- take k imports]
           ]
        ++ [ Diagnostic l "%recover expects a label and a rule name"
           | (l, "recover", a) <- directives
           , not (T.null a)
           , case T.words a of
               [lab, rule] -> not (isValidIdent lab && isValidIdent rule)
               _ -> True
           ]
        ++ [ Diagnostic l ("%language expects extension names, but got " <> x)
           | ("language", al, a) <- argLocs
           , Located l x <- splitExports al a
           , not (isExtensionName x)
           ]
        -- ADR 0080: the values that the generated module has as written
        ++ [ Diagnostic al ("%module expects a module name, but got " <> a)
           | ("module", al, a) <- argLocs
           , not (T.null a)
           , not (isModuleName a)
           ]
        ++ [ Diagnostic l ("%export expects export items, but got " <> x)
           | ("export", al, a) <- argLocs
           , Located l x <- splitExports al a
           , not (isExportItem recursiveDoEnabled x)
           ]
        -- ADR 0075
        ++ [ Diagnostic l ("%deriving expects class names, but got " <> x)
           | ("deriving", al, a) <- argLocs
           , Located l x <- splitExports al a
           , not (isClassName x)
           ]
        ++ [d | (_, Left d) <- expects ++ messages]
        ++ [ Diagnostic l ("duplicate %" <> d <> " for " <> what <> " " <> n)
           | (d, what, xs) <- [("expect", "rule", expects), ("message", "label", messages)]
           , (k, (l, Right (Located _ n, _))) <- zip [0 :: Int ..] xs
           , n `elem` [m | (_, Right (Located _ m, _)) <- take k xs]
           ]
        ++ [ Diagnostic l "%safe expects a label name"
           | (l, "safe", a) <- directives
           , not (T.null a)
           , not (isValidIdent a)
           ]
        ++ [ Diagnostic l ("%" <> n <> " expects a rule name")
           | (l, n, a) <- directives
           , n `elem` ["start", "entry", "nomemo", "token", "trivia", "inline"]
           , not (T.null a)
           , not (isValidIdent a)
           ]
        ++ [ Diagnostic l "%tabstop expects a positive integer"
           | Just (Located l a) <- [single "tabstop"]
           , not (T.all isDigit a) || T.null a || T.all (== '0') a
           ]
        ++ [ Diagnostic l ("rule " <> n <> " has parameters, so it needs a type annotation")
           | (l, n, _) <- defs
           , not (M.member n annots)
           , not (null (templateNamesOf n))
           ]
        ++ [ Diagnostic l ("rule " <> n <> " has a type annotation but no definition")
           | (n, (l, _, _, _) : _) <- M.toList annots
           , not (M.member n defCounts)
           ]
        ++ [ Diagnostic l ("duplicate type annotation for " <> n)
           | (n, _ : (l, _, _, _) : _) <- M.toList annots
           ]
        ++ [ Diagnostic l ("duplicate definition of " <> n)
           | (n, c) <- M.toList defCounts
           , c > 1
           , (l, _, _) : _ <- [drop 1 [d | d@(_, n', _) <- defs, n' == n]]
           ]
        ++ [Diagnostic (Loc 0 1 1) "the grammar has no rules" | null defs, isJust moduleName]
        -- ADR 0031
        ++ [ Diagnostic dl ("the template parameters of the definition of " <> n <> " do not match its type annotation")
           | (n, (dl, tns)) <- M.toList defTemplateNames
           , Just ((_, _, tps, _) : _) <- [M.lookup n annots]
           , tns /= map templateParamName tps
           ]

-- | Whether a text is a path that @%import@ accepts (ADR 0092): one or more
-- parts separated by @/@, not starting with @/@, each part a non-empty run
-- of ASCII letters, digits, @_@, @-@ and @.@ other than @.@ and @..@, and
-- the last part ending in @.hpeg@. Such a path names a file in the
-- directory of the grammar or under it, and two paths name the same file
-- when they are the same.
--
-- @
-- isImportPath \"lex\/Ident.hpeg\" == True
-- isImportPath \"..\/x.hpeg\" == False
-- @
isImportPath :: Text -> Bool
isImportPath t = all part parts && ".hpeg" `T.isSuffixOf` t
  where
    parts = T.splitOn "/" t
    part p = not (T.null p) && p `notElem` [".", ".."] && T.all (\c -> isAscii c && (isAlphaNum c || c `elem` ("_-." :: String))) p

-- The lexical form of a GHC language extension name.
isExtensionName :: Text -> Bool
isExtensionName t = case T.uncons t of
  Just (c, rest) -> isAsciiUpper c && T.all (\x -> isAscii x && isAlphaNum x) rest
  Nothing -> False

-- The lexical form of a class name, which may be qualified: @Eq@,
-- @GHC.Generics.Generic@.
isClassName :: Text -> Bool
isClassName t = not (T.null t) && all part (T.splitOn "." t)
  where
    part p = case T.uncons p of
      Just (c, rest) -> isUpper c && T.all isIdentChar rest
      Nothing -> False

-- | A module name: parts separated by dots, each of which starts with an
-- upper case letter, followed by letters, digits, @_@ and @'@ (ADR 0080).
isModuleName :: Text -> Bool
isModuleName = isClassName

-- The lexical form of an item of an export list (ADR 0014, ADR 0080): a
-- name that may be qualified, a type name followed by @(..)@ or by names
-- and operators in parentheses, an operator in parentheses, any of them
-- after @type@ or @pattern@, and @module@ with a module name. Spaces and
-- tabs may separate the parts. A comment, a newline or @where@ fits none
-- of these forms.
isExportItem :: Bool -> Text -> Bool
isExportItem recursiveDoEnabled t = not (any (`T.isInfixOf` t) ["--", "{-", "-}"]) && maybe False null (item (tokens (T.unpack t)))
  where
    item = \case
      "module" : m : rest | isModuleName (T.pack m) -> Just rest
      kw : rest | kw `elem` ["type", "pattern"] -> plain rest
      ts -> plain ts
    -- A name with an optional list, or an operator in parentheses.
    plain = \case
      "(" : op : ")" : rest | isOperator op -> Just rest
      n : "(" : ".." : ")" : rest | isTypeName n -> Just rest
      n : "(" : rest | isTypeName n -> names rest
      n : rest | isQualifiedName n -> Just rest
      _ -> Nothing
    -- The names and operators of a list, separated by commas, up to ")".
    names ts = do
      rest <- member ts
      case rest of
        "," : more -> names more
        ")" : more -> Just more
        _ -> Nothing
    member = \case
      "(" : op : ")" : rest | isOperator op -> Just rest
      n : rest | isValidIdent (T.pack n) && T.pack n `notElem` reservedWords -> Just rest
      _ -> Nothing
    isTypeName n = isQualifiedName n && maybe False isUpper (fmap fst (T.uncons (T.takeWhileEnd (/= '.') (T.pack n))))
    -- A variable or a type name, after a module name and a dot.
    isQualifiedName n = case T.breakOnEnd "." (T.pack n) of
      ("", name) -> isValidIdent name && name `notElem` reservedWords
      (qual, name) -> isModuleName (T.dropEnd 1 qual) && isValidIdent name
        && name /= "do" && (not recursiveDoEnabled || name /= "mdo")
    isOperator op = not (null op) && all isSymbolChar op
    isSymbolChar c = c `elem` ("!#$%&*+./<=>?@\\^|-~:" :: String)
    -- Parentheses and commas are tokens of their own, as is "..".
    tokens = \case
      [] -> []
      c : cs
        | c == ' ' || c == '\t' -> tokens cs
        | c `elem` ("()," :: String) -> [c] : tokens cs
        | otherwise ->
            let (w, rest) = break (\x -> x `elem` (" \t()," :: String)) (c : cs)
             in w : tokens rest

-- Split export items at top-level commas.
splitExports :: Loc -> Text -> [Located Text]
splitExports l0 t = go l0 (T.unpack t) (0 :: Int) Nothing [] []
  where
    -- The location of each item is that of its first non-space character.
    go _ [] _ start cur acc = reverse (finish start cur acc)
    go l (c : cs) d start cur acc
      | c == ',' && d == 0 = go (adv l) cs d Nothing [] (finish start cur acc)
      | c == ' ' && null cur = go (adv l) cs d start cur acc
      | otherwise =
          let d' = if c `elem` ("([" :: String) then d + 1 else if c `elem` (")]" :: String) then d - 1 else d
              start' = maybe (Just l) Just start
           in go (adv l) cs d' start' (c : cur) acc
    adv (Loc f ln col) = Loc f ln (col + 1)
    finish start cur acc =
      let s = T.strip (T.pack (reverse cur))
       in case start of
            Just l | not (T.null s) -> Located l s : acc
            _ -> acc
