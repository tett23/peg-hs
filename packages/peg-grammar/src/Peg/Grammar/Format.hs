{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The formatter of the @.hpeg@ notation (ADR 0032).
--
-- There is one style and no option. The formatter rewrites spaces and line
-- breaks only: the tokens, the comments and the Haskell fragments are kept,
-- and so is the order of the directives, rules and alternatives. It reads
-- the grammar with a parser generated from @grammar/PegSyntax.hpeg@, the
-- notation's grammar with a lossless syntax tree (ADR 0019), so that the
-- comments are found where they are written.
--
-- 'formatGrammar' is what @peg-hs fmt@ and the formatting of the language
-- server run:
--
-- @
-- case formatGrammar src of
--   Left diags -> mapM_ (TIO.putStrLn . renderDiagnostic \"Calc.hpeg\") diags
--   Right out -> when (out /= src) (TIO.writeFile \"Calc.hpeg\" out)
-- @
--
-- 'sameGrammar' and 'grammarComments' are the comparisons the formatter's
-- result must pass, exposed for its tests.
module Peg.Grammar.Format
  ( formatGrammar
  , grammarComments
  , sameGrammar
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Assemble (Top (..), isIdentChar)
import Peg.Grammar.Parser (parseTops)
import qualified Peg.Grammar.SelfHostedSyntax as S
import Peg.Runtime.Syntax

-- | Format a grammar. CRLF line breaks become LF. A grammar with a syntax
-- error is not formatted and its error is returned, as by
-- 'Peg.Grammar.Parser.parseGrammar'; other errors of the grammar do not
-- stop formatting. The result is parsed again and compared with the
-- grammar; if they differ, which is a bug of the formatter, an error is
-- returned instead of the result.
formatGrammar :: Text -> Either [Diagnostic] Text
formatGrammar input = do
  let src = T.replace "\r\n" "\n" input
  _ <- parseTops src
  root <- either (const (Left [internalError "the syntax tree parser rejected the grammar"])) Right (S.parseSyntax src)
  let out = render (walk root)
  if sameGrammar src out
    then Right out
    else Left [internalError "formatting would change the grammar"]
  where
    internalError m = Diagnostic (Loc 1 1) ("internal error of the formatter: " <> m)

-- | The comments of a grammar in order, without trailing spaces. The empty
-- list for a grammar with a syntax error.
grammarComments :: Text -> [Text]
grammarComments src = either (const []) comments (S.parseSyntax (T.replace "\r\n" "\n" src))
  where
    comments n
      | kindOf n == "Directive" = maybe [] pure (snd (directiveParts (syntaxText n)))
      | otherwise = concatMap commentsIn (syntaxChildrenWithTokens n)
    commentsIn = \case
      NodeElement n -> comments n
      TokenElement t
        | tokenKindName t == "Comment" -> [T.stripEnd (tokenText t)]
        | otherwise -> []

-- | Whether two grammars have the same top-level items, ignoring locations
-- and the spaces around the code of one-line actions.
sameGrammar :: Text -> Text -> Bool
sameGrammar a b = case (parseTops a, parseTops b) of
  (Right x, Right y) -> map eraseTop x == map eraseTop y
  _ -> False

-- Comparison ------------------------------------------------------------------

eraseTop :: Top -> Top
eraseTop = \case
  TDirective _ n _ a -> TDirective z n z a
  TVerbatim _ b -> TVerbatim z b
  TAnnot _ n ps tps ty -> TAnnot z n [Param pn (erase t) | Param pn t <- ps] tps (erase ty)
  TDef _ n tps as -> TDef z n tps (map alt as)
  where
    z = Loc 0 0
    erase (Located _ x) = Located z x
    alt (Alt _ is a) = Alt z (map item is) (fmap (\(Located _ c) -> Located z (oneLine c)) a)
    oneLine c = if T.any (== '\n') c then c else T.strip c
    item (Item _ b e) = Item z b (expr e)
    expr = \case
      ERef _ n as -> ERef z n (map erase as)
      EGroup g -> EGroup (map (map item) g)
      EStar e -> EStar (expr e)
      EPlus e -> EPlus (expr e)
      EOpt e -> EOpt (expr e)
      EAnd e -> EAnd (expr e)
      ENot e -> ENot (expr e)
      ECapture e -> ECapture (expr e)
      ELabel _ e l -> ELabel z (expr e) l
      EPred p c -> EPred p (erase c)
      ETemplate _ n as -> ETemplate z n (map expr as)
      EDiscard e -> EDiscard (expr e)
      e -> e

-- The layout ------------------------------------------------------------------

-- What separates two tokens, from the least to the most. 'GSoft' is a space,
-- or a line break where the author wrote one. 'GKeep' is a line break, and a
-- blank line where the author wrote one. 'GBlank' is a blank line.
data Gap = GNone | GSpace | GSoft | GLine | GKeep | GBlank | GEnd
  deriving (Eq, Ord)

data Event
  = Tok Text
  | Gap Gap
  | Space Text
  | Comment Text
  | -- | Indent the following lines at the current column.
    PushHere
  | -- | Indent the following lines further than the current indentation.
    PushRel Int
  | Pop

kindOf :: SyntaxNode -> Text
kindOf = S.nameOfSyntaxKind . syntaxKind

tokenKindName :: SyntaxToken -> Text
tokenKindName = S.nameOfSyntaxKind . tokenKind

isNode :: Text -> SyntaxElement -> Bool
isNode k = \case
  NodeElement n -> kindOf n == k
  TokenElement _ -> False

isTok :: Text -> SyntaxElement -> Bool
isTok s = \case
  TokenElement t -> tokenKind t == textKind && tokenText t == s
  NodeElement _ -> False

isTokKind :: Text -> SyntaxElement -> Bool
isTokKind k = \case
  TokenElement t -> tokenKindName t == k
  NodeElement _ -> False

element :: SyntaxElement -> [Event]
element = \case
  NodeElement n -> walk n
  TokenElement t -> case tokenKindName t of
    "SpaceChar" -> [Space (tokenText t)]
    "Comment" -> [Comment (T.stripEnd (tokenText t))]
    _ -> [Tok (tokenText t)]

walk :: SyntaxNode -> [Event]
walk n = case kindOf n of
  "File" -> file es
  "Directive" -> [Tok (directive (syntaxText n))]
  "Verbatim" -> [Tok (verbatim (syntaxText n))]
  "Action" -> [Tok (action (syntaxText n))]
  "Declaration" -> declaration es
  "Alts" -> concatMap (\e -> if isNode "Alt" e then alternative e else element e) es
  "MoreAlt" -> concatMap (\e -> if isTok "/" e then [Gap GLine, Tok "/", Gap GSpace] else if isNode "Alt" e then alternative e else element e) es
  "Alt" -> sequenceOf GNone es
  "MoreGroup" -> sequenceOf GSpace es
  "GroupAlts" -> sequenceOf GNone es
  "Labeled" -> concatMap (\e -> if isNode "LabelPart" e then Gap GSpace : element e else element e) es
  "Primary" -> concatMap (\e -> if isNode "GroupAlts" e then PushHere : element e else if isTok ")" e then element e ++ [Pop] else element e) es
  "TemplateArgs" -> commaList "TemplateArg" (\e -> PushHere : element e ++ [Pop]) es
  "TemplateParams" -> commaList "TemplateParam" element es
  "TemplateParam" -> spaced es
  "ParamChunks" -> concatMap (\e -> if isNode "ParamChunks" e then Gap GSpace : element e else element e) es
  "ArgChunks" -> concatMap (\e -> if isNode "ArgChunks" e then Gap GSpace : element e else element e) es
  _ -> concatMap element es
  where
    es = syntaxChildrenWithTokens n
    alternative e = PushRel 2 : element e ++ [Pop]

-- The top-level items: a blank line between rules, none between the
-- annotation and the definition of a rule, and the author's blank lines
-- between directives.
file :: [SyntaxElement] -> [Event]
file = go Nothing
  where
    go _ [] = [Gap GEnd]
    go prev (e : rest) = case e of
      NodeElement n | kindOf n `elem` ["Directive", "Verbatim", "Declaration"] -> Gap (between prev n) : element e ++ go (Just n) rest
      _ -> element e ++ go prev rest
    between Nothing _ = GKeep
    between (Just p) c
      | directiveLike p && directiveLike c = GKeep
      | Just a <- declName "::" p, Just d <- declName "<-" c, a == d = GLine
      | otherwise = GBlank
    directiveLike n = kindOf n `elem` ["Directive", "Verbatim"]
    declName op n
      | kindOf n == "Declaration" && any (isTok op) es =
          case [tokenText t | TokenElement t <- es, tokenKindName t == "Ident"] of
            name : _ -> Just name
            [] -> Nothing
      | otherwise = Nothing
      where
        es = syntaxChildrenWithTokens n

declaration :: [SyntaxElement] -> [Event]
declaration = \case
  [] -> []
  e : rest
    | isTok "::" e -> Gap GSpace : element e ++ declaration rest
    | isTokKind "InlineSp" e -> declaration rest
    | TokenElement t <- e, tokenKindName t == "TypeText" -> [Gap GSpace, Tok (T.stripEnd (tokenText t))] ++ declaration rest
    | isTok "<-" e -> [Gap GSpace, PushHere, Tok "<-", Gap GSpace] ++ declaration rest ++ [Pop]
    | otherwise -> element e ++ declaration rest

-- The items of a sequence, and its action: the first after the given gap,
-- the others after a space or the author's line break.
sequenceOf :: Gap -> [SyntaxElement] -> [Event]
sequenceOf first = go False
  where
    go _ [] = []
    go seen (e : rest)
      | isNode "Item" e || isNode "Action" e = Gap (if seen then GSoft else first) : element e ++ go True rest
      | isTok "/" e = Gap GSpace : element e ++ go seen rest
      | otherwise = element e ++ go seen rest

-- Elements of the given kind separated by commas, with a space after each
-- comma.
commaList :: Text -> (SyntaxElement -> [Event]) -> [SyntaxElement] -> [Event]
commaList k f = go False
  where
    go _ [] = []
    go afterComma (e : rest)
      | isNode k e = (if afterComma then (Gap GSpace :) else id) (f e) ++ go False rest
      | isTok "," e = element e ++ go True rest
      | otherwise = element e ++ go afterComma rest

-- Tokens separated by one space.
spaced :: [SyntaxElement] -> [Event]
spaced = go False
  where
    go _ [] = []
    go seen (e : rest) = case element e of
      evs@(Tok _ : _) -> (if seen then (Gap GSpace :) else id) evs ++ go True rest
      evs -> evs ++ go seen rest

-- @%name argument # comment@, with one space between them.
directive :: Text -> Text
directive t =
  let (name, _) = T.span isIdentChar (T.drop 1 t)
      (arg, comment) = directiveParts t
   in T.concat ["%", name, if T.null arg then "" else " " <> arg, maybe "" (" " <>) comment]

-- The argument of a directive and its comment.
directiveParts :: Text -> (Text, Maybe Text)
directiveParts t =
  let (name, rest) = T.span isIdentChar (T.drop 1 t)
      raw = T.strip rest
      (a, c) = T.breakOn "#" raw
   in if name /= "env" && not (T.null c) then (T.strip a, Just (T.stripEnd c)) else (raw, Nothing)

-- @%{@ and @}%@ on their own lines.
verbatim :: Text -> Text
verbatim t =
  let body = T.dropEnd 2 (T.drop 2 t)
      opened = if "\n" `T.isPrefixOf` body then body else "\n" <> T.stripStart body
      trimmed = T.dropWhileEnd (`elem` [' ', '\t']) opened
      closed = if "\n" `T.isSuffixOf` trimmed then trimmed else trimmed <> "\n"
   in "%{" <> closed <> "}%"

-- @{ code }@ for a one-line action; a multi-line one is kept.
action :: Text -> Text
action t =
  let code = T.dropEnd 1 (T.drop 1 t)
   in if T.any (== '\n') code
        then t
        else if T.null (T.strip code) then "{}" else "{ " <> T.strip code <> " }"

-- Rendering -------------------------------------------------------------------

data Trivium = Newlines Int | Remark Text

data R = R
  { rOut :: [Text]
  , rCol :: !Int
  , rLineStart :: !Bool
  , rFileStart :: !Bool
  , rStack :: [Int]
  , rGap :: Gap
  , rTrivia :: [Trivium]
  }

render :: [Event] -> Text
render = T.concat . reverse . rOut . flush . foldl step (R [] 0 True True [0] GNone [])
  where
    step r = \case
      Tok t -> emit t (flush r)
      Gap g -> r {rGap = max g (rGap r)}
      Space s -> r {rTrivia = Newlines (T.count "\n" s) : rTrivia r}
      Comment c -> r {rTrivia = Remark c : rTrivia r}
      PushHere -> let r' = flush r in r' {rStack = rCol r' : rStack r'}
      PushRel k -> r {rStack = (indent r + k) : rStack r}
      Pop -> r {rStack = drop 1 (rStack r)}

indent :: R -> Int
indent r = case rStack r of
  i : _ -> i
  [] -> 0

emit :: Text -> R -> R
emit t r =
  let pad = if rLineStart r then T.replicate (rCol r) " " else ""
      col = case T.breakOnEnd "\n" t of
        ("", _) -> rCol r + T.length t
        (_, lastLine) -> T.length lastLine
   in r {rOut = t : pad : rOut r, rCol = col, rLineStart = False, rFileStart = False}

newlines :: Int -> R -> R
newlines k r = r {rOut = T.replicate k "\n" : rOut r, rCol = indent r, rLineStart = True}

-- Write the pending gap and the comments before it.
flush :: R -> R
flush r0 =
  let ts = reverse (rTrivia r0)
      g = case rGap r0 of
        GSoft -> if any (\case Newlines k -> k > 0; Remark _ -> False) ts then GLine else GSpace
        x -> x
      r1 = r0 {rGap = GNone, rTrivia = []}
      (r2, nl, wrote, own) = foldl (comment g) (r1, 0, False, False) ts
   in finish g nl wrote own r2
  where
    comment g (r, nl, wrote, own) = \case
      Newlines k -> (r, nl + k, wrote, own)
      Remark c
        | nl == 0 && not (rLineStart r) -> (emit (" " <> c) r, 0, True, own)
        | rFileStart r -> (emit c r, 0, True, True)
        | otherwise ->
            let blank = case g of
                  GBlank -> not own || nl >= 2
                  GKeep -> nl >= 2
                  GEnd -> nl >= 2
                  _ -> False
             in (emit c (newlines (if blank then 2 else 1) r), 0, True, True)
    finish g nl wrote own r
      | g == GEnd = newlines 1 r
      | rFileStart r = r
      | wrote || g >= GLine =
          let blank = case g of
                GBlank -> not own
                GKeep -> nl >= 2
                _ -> False
           in newlines (if blank then 2 else 1) r
      | g == GSpace && not (rLineStart r) = emit " " r
      | otherwise = r
