-- | The language server as a pure function from its state and a message to
-- the new state and the messages to send (ADR 0035).
--
-- The server supports diagnostics (pushed on @didOpen@ and @didChange@,
-- with full text synchronisation), formatting, semantic tokens, go to
-- definition, references, hover and document symbols. Positions are
-- counted in UTF-16 code units, or in bytes when the client offers
-- @utf-8@ in @positionEncodings@.
--
-- Start from 'initialState' and pass each message to 'handleFrame' (for
-- the output of 'Peg.Lsp.Rpc.decodeFrames') or 'handleMessage' (for a
-- parsed message); send the messages of the t'Step' and stop when
-- 'stepExit' is set. "Peg.Lsp" does this over handles; a test can do it
-- with values:
--
-- @
-- let open = object
--       [ (\"jsonrpc\", String \"2.0\"), (\"method\", String \"textDocument\/didOpen\")
--       , (\"params\", object [(\"textDocument\", object [(\"uri\", String \"file:\/\/\/a.peg\"), (\"text\", String src)])])
--       ]
--     s1 = handleMessage initialState (object [(\"jsonrpc\", String \"2.0\"), (\"id\", int 1), (\"method\", String \"initialize\"), (\"params\", object [])])
--     s2 = handleMessage (stepState s1) open
-- in stepOutput s2  -- [the textDocument\/publishDiagnostics notification]
-- @
--
-- 'diagnose' is the analysis behind the diagnostics, usable on its own.
module Peg.Lsp.Server
  ( State
  , initialState
  , Step (..)
  , handleFrame
  , handleMessage
  , Severity (..)
  , diagnose
  , tokenTypes
  , tokenModifiers
  ) where

import Data.Bits (shiftL, (.|.))
import qualified Data.ByteString as BS
import Data.Char (isSpace, ord)
import Data.List (find, nub, sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust, listToMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Peg.Grammar (Diagnostic (..), Loc (..))
import Peg.Grammar.Assemble (isIdentChar)
import Peg.Grammar.Check (check)
import Peg.Grammar.Format (formatGrammar)
import Peg.Grammar.Highlight
import Peg.Grammar.Labels (labelWarnings)
import Peg.Grammar.Lint (LintWarning (..), lintGrammar)
import Peg.Grammar.Outline
import Peg.Grammar.Parser (parseGrammar, parseTops)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Peg.Lsp.Json

-- | How positions count characters (LSP 3.17 @positionEncoding@).
data Encoding = Utf8 | Utf16
  deriving (Eq, Show)

data Document = Document
  { docText :: Text
  , docLines :: [Text]
  , docOutline :: Outline
  -- ^ Computed when first used, and kept until the document changes.
  }

-- | The state of the server: the open documents, the position encoding
-- agreed on in @initialize@, and whether @initialize@ and @shutdown@ have
-- been received. Opaque; start from 'initialState'.
data State = State
  { stDocuments :: M.Map Text Document
  , stEncoding :: Encoding
  , stInitialized :: Bool
  , stShutdown :: Bool
  }

-- | The state before @initialize@: no document is open. Requests other
-- than @initialize@ are answered with an error until it arrives.
initialState :: State
initialState = State M.empty Utf16 False False

-- | The result of handling a message: the new state, the messages to send,
-- and the exit status when the server must stop.
data Step = Step
  { stepState :: State
  , stepOutput :: [Value]
  , stepExit :: Maybe Int
  }

-- | Handle the body of a framed message, or an error of the framing (see
-- 'Peg.Lsp.Rpc.decodeFrames'). A framing error or a body that is not JSON
-- is answered with a parse error (-32700).
handleFrame :: State -> Either Text Text -> Step
handleFrame st = \case
  Left err -> Step st [errorResponse Null (-32700) err] Nothing
  Right body -> case parseJson body of
    Nothing -> Step st [errorResponse Null (-32700) "the message is not JSON"] Nothing
    Just v -> handleMessage st v

-- | Handle a parsed message: a request (with an @id@), which gets a
-- response, or a notification. A message without a method is ignored.
handleMessage :: State -> Value -> Step
handleMessage st msg =
  case (member "method" msg >>= asText, member "id" msg) of
    (Nothing, _) -> Step st [] Nothing
    (Just m, Just i) -> request st m i params
    (Just m, Nothing) -> notification st m params
  where
    params = fromMaybe Null (member "params" msg)

request :: State -> Text -> Value -> Value -> Step
request st method i params
  | method == "initialize" =
      let enc = if any (== String "utf-8") (fromMaybe [] (path ["capabilities", "general", "positionEncodings"] params >>= asArray)) then Utf8 else Utf16
       in Step st {stEncoding = enc, stInitialized = True} [response i (initializeResult enc)] Nothing
  | not (stInitialized st) = Step st [errorResponse i (-32002) "the server is not initialized"] Nothing
  | stShutdown st = Step st [errorResponse i (-32600) "the server is shutting down"] Nothing
  | method == "shutdown" = Step st {stShutdown = True} [response i Null] Nothing
  | otherwise = case lookup method handlers of
      Just h -> Step st [response i (fromMaybe Null (document >>= \(uri, d) -> h (stEncoding st) uri d params))] Nothing
      Nothing -> Step st [errorResponse i (-32601) ("unknown method " <> method)] Nothing
  where
    document = do
      uri <- path ["textDocument", "uri"] params >>= asText
      d <- M.lookup uri (stDocuments st)
      pure (uri, d)
    handlers =
      [ ("textDocument/formatting", formatting)
      , ("textDocument/semanticTokens/full", semanticTokens)
      , ("textDocument/definition", definition)
      , ("textDocument/references", references)
      , ("textDocument/hover", hover)
      , ("textDocument/documentSymbol", documentSymbols)
      ]

notification :: State -> Text -> Value -> Step
notification st method params = case method of
  "exit" -> Step st [] (Just (if stShutdown st then 0 else 1))
  "textDocument/didOpen"
    | Just uri <- path ["textDocument", "uri"] params >>= asText
    , Just text <- path ["textDocument", "text"] params >>= asText ->
        open uri text
  "textDocument/didChange"
    | Just uri <- path ["textDocument", "uri"] params >>= asText
    , Just changes <- member "contentChanges" params >>= asArray
    , Just text <- listToMaybe (reverse (mapMaybe (\c -> member "text" c >>= asText) changes)) ->
        open uri text
  "textDocument/didClose"
    | Just uri <- path ["textDocument", "uri"] params >>= asText ->
        Step st {stDocuments = M.delete uri (stDocuments st)} [publish uri []] Nothing
  _ -> Step st [] Nothing
  where
    open uri text =
      let d = newDocument text
       in Step st {stDocuments = M.insert uri d (stDocuments st)} [publish uri (map (diagnosticValue (stEncoding st) d) (diagnose text))] Nothing

newDocument :: Text -> Document
newDocument text = Document text (T.splitOn "\n" text) (outline text)

-- Messages ----------------------------------------------------------------------

response :: Value -> Value -> Value
response i result = object [("jsonrpc", String "2.0"), ("id", i), ("result", result)]

errorResponse :: Value -> Int -> Text -> Value
errorResponse i code msg = object [("jsonrpc", String "2.0"), ("id", i), ("error", object [("code", int code), ("message", String msg)])]

publish :: Text -> [Value] -> Value
publish uri ds =
  object
    [ ("jsonrpc", String "2.0")
    , ("method", String "textDocument/publishDiagnostics")
    , ("params", object [("uri", String uri), ("diagnostics", Array ds)])
    ]

initializeResult :: Encoding -> Value
initializeResult enc =
  object
    [ ( "capabilities"
      , object
          [ ("positionEncoding", String (if enc == Utf8 then "utf-8" else "utf-16"))
          , ("textDocumentSync", object [("openClose", Bool True), ("change", int 1)])
          , ("documentFormattingProvider", Bool True)
          , ("semanticTokensProvider", object [("legend", object [("tokenTypes", Array (map String tokenTypes)), ("tokenModifiers", Array (map String tokenModifiers))]), ("full", Bool True)])
          , ("definitionProvider", Bool True)
          , ("referencesProvider", Bool True)
          , ("hoverProvider", Bool True)
          , ("documentSymbolProvider", Bool True)
          ]
      )
    , ("serverInfo", object [("name", String "peg-hs")])
    ]

-- Diagnostics ---------------------------------------------------------------------

-- | The severity of a diagnostic of 'diagnose'.
data Severity
  = -- | An error of @peg-hs gen@: the grammar cannot be generated.
    Error
  | -- | A warning of the label check or of @peg-hs lint@.
    Warning
  deriving (Eq, Show)

-- | The diagnostics of a grammar with the messages and locations of
-- @peg-hs gen@ and @peg-hs lint@, and the code of a lint rule
-- ('Peg.Grammar.Lint.lintRule'). An error stops the checks as in
-- @peg-hs gen@: a grammar with an error has no warnings. A grammar
-- with a syntax error has only its syntax errors: the first is the one of
-- @peg-hs gen@, followed by those that recovery finds on later lines.
diagnose :: Text -> [(Severity, Diagnostic, Maybe Text)]
diagnose src = case parseTops src of
  Left ds@(d : _) ->
    map (\x -> (Error, x, Nothing)) ds
      ++ [(Error, e, Nothing) | e <- outlineSyntaxErrors (outline src), locLine (diagLoc e) > locLine (diagLoc d)]
  Left [] -> []
  Right _ -> case parseGrammar src >>= \g0 -> either (Left . templateNotes g0) (Right . (,) g0) (expandTemplates g0 >>= \g -> g <$ check g) of
    Left ds -> map (\x -> (Error, x, Nothing)) ds
    Right (g0, g) ->
      [(Warning, w, Nothing) | w <- templateNotes g0 (labelWarnings g)]
        ++ [ (Warning, Diagnostic (lintLoc w) (lintMessage w <> " [" <> lintRule w <> "]; " <> lintHint w), Just (lintRule w))
           | w <- lintGrammar g0
           ]

diagnosticValue :: Encoding -> Document -> (Severity, Diagnostic, Maybe Text) -> Value
diagnosticValue enc d (sev, Diagnostic l@(Loc line col) msg, code) =
  object $
    [ ("range", rangeValue enc d l (Loc line (col + max 1 (T.length (T.takeWhile isIdentChar (T.drop (col - 1) (lineAt d line)))))))
    , ("severity", int (if sev == Error then 1 else 2))
    , ("source", String "peg-hs")
    , ("message", String msg)
    ]
      ++ [("code", String c) | Just c <- [code]]

-- Positions -----------------------------------------------------------------------

lineAt :: Document -> Int -> Text
lineAt d n = fromMaybe "" (listToMaybe (drop (n - 1) (docLines d)))

units :: Encoding -> Text -> Int
units Utf8 t = BS.length (TE.encodeUtf8 t)
units Utf16 t = T.foldl' (\n c -> n + if ord c > 0xFFFF then 2 else 1) 0 t

positionValue :: Encoding -> Document -> Loc -> Value
positionValue enc d (Loc l c) = object [("line", int (l - 1)), ("character", int (units enc (T.take (c - 1) (lineAt d l))))]

rangeValue :: Encoding -> Document -> Loc -> Loc -> Value
rangeValue enc d a b = object [("start", positionValue enc d a), ("end", positionValue enc d b)]

-- The location of a position of the protocol.
locOf :: Encoding -> Document -> Value -> Maybe Loc
locOf enc d v = do
  line <- member "line" v >>= asInt
  ch <- member "character" v >>= asInt
  let text = lineAt d (line + 1)
      go c n t = case T.uncons t of
        Just (x, rest) | n + units enc (T.singleton x) <= ch -> go (c + 1) (n + units enc (T.singleton x)) rest
        _ -> c
  pure (Loc (line + 1) (go 1 0 text))

within :: Loc -> Loc -> Loc -> Bool
within p a b = a <= p && p <= b

-- Features ------------------------------------------------------------------------

type Handler = Encoding -> Text -> Document -> Value -> Maybe Value

formatting :: Handler
formatting enc _ d _ = Just $ case formatGrammar (docText d) of
  Right out
    | out /= docText d ->
        let lastLine = length (docLines d)
            end = Loc lastLine (T.length (lineAt d lastLine) + 1)
         in Array [object [("range", rangeValue enc d (Loc 1 1) end), ("newText", String out)]]
  _ -> Array []

-- | The token types of the semantic tokens, in the order of their indices,
-- as announced in the legend of the @initialize@ response.
tokenTypes :: [Text]
tokenTypes = ["function", "macro", "parameter", "variable", "string", "regexp", "keyword", "operator", "decorator", "comment"]

-- | The token modifiers, in the order of their bits.
tokenModifiers :: [Text]
tokenModifiers = ["declaration", "definition", "defaultLibrary"]

semanticTokens :: Handler
semanticTokens enc _ d _ =
  let o = docOutline d
      tokens = sortOn (\(a, _, _, _) -> a) (mapMaybe (classify o) (outlineHighlights o))
      encoded = go (Loc 1 1) tokens
      go _ [] = []
      go (Loc pl pc) ((a@(Loc l c), Loc _ ec, ty, mods) : rest) =
        let prefix = units enc (T.take (c - 1) (lineAt d l))
            prevPrefix = if l == pl then units enc (T.take (pc - 1) (lineAt d l)) else 0
            len = units enc (T.take (ec - c) (T.drop (c - 1) (lineAt d l)))
         in [l - pl, prefix - prevPrefix, len, index ty tokenTypes, foldl (.|.) 0 [1 `shiftL` index m tokenModifiers | m <- mods]] ++ go a rest
      index x xs = length (takeWhile (/= x) xs)
   in Just (object [("data", Array (map int encoded))])

-- The type and modifiers of a highlight; Haskell code and brackets have none.
classify :: Outline -> Highlight -> Maybe (Loc, Loc, Text, [Text])
classify o h = case hlKind h of
  HRuleName -> do
    decl <- find (\x -> declNameStart x == start) (outlineDeclarations o)
    let defined = declKind decl == Definition
    pure $
      if isTemplate (declName decl)
        then (start, end, "macro", ["definition" | defined])
        else (start, end, "function", if defined then ["definition"] else ["declaration"])
  HRuleReference
    | any (\x -> declKind x == Definition && within start (declStart x) (declEnd x) && maybe False (elem name) (declTemplateParams x)) (outlineDeclarations o) ->
        Just (start, end, "parameter", [])
    | isTemplate name -> Just (start, end, "macro", [])
    | otherwise -> Just (start, end, "function", [])
  HTemplateParameter -> Just (start, end, "parameter", ["declaration"])
  HBinding -> Just (start, Loc (locLine end) (locColumn end - 1), "variable", ["declaration"])
  HReservedBinding -> Just (start, end, "variable", ["defaultLibrary"])
  HLiteral -> Just (start, end, "string", [])
  HClass -> Just (start, end, "regexp", [])
  HDirective -> Just (start, end, "keyword", [])
  HOperator -> Just (start, end, "operator", [])
  HChoice -> Just (start, end, "operator", [])
  HDefinition -> Just (start, end, "operator", [])
  HLabel -> Just (start, end, "decorator", [])
  HComment | locLine start == locLine end -> Just (start, end, "comment", [])
  _ -> Nothing
  where
    start = hlStart h
    end = hlEnd h
    name = maybe "" id (lookup start [(refStart r, refName r) | r <- outlineReferences o])
    isTemplate n = any (\x -> declName x == n && isJust (declTemplateParams x)) (outlineDeclarations o)

-- The name of the rule at a position: a reference or a declaration's name,
-- with its range.
nameAt :: Document -> Loc -> Maybe (Text, Loc, Loc)
nameAt d p =
  listToMaybe $
    [(refName r, refStart r, refEnd r) | r <- outlineReferences o, within p (refStart r) (refEnd r)]
      ++ [(declName x, declNameStart x, declNameEnd x) | x <- outlineDeclarations o, within p (declNameStart x) (declNameEnd x)]
  where
    o = docOutline d

location :: Encoding -> Text -> Document -> Loc -> Loc -> Value
location enc uri d a b = object [("uri", String uri), ("range", rangeValue enc d a b)]

definition :: Handler
definition enc uri d params = do
  p <- member "position" params >>= locOf enc d
  (name, _, _) <- nameAt d p
  let decls = [x | x <- outlineDeclarations (docOutline d), declName x == name]
  x <- listToMaybe ([x | x <- decls, declKind x == Definition] ++ decls)
  pure (location enc uri d (declNameStart x) (declNameEnd x))

references :: Handler
references enc uri d params = do
  p <- member "position" params >>= locOf enc d
  (name, _, _) <- nameAt d p
  let withDecl = fromMaybe False (path ["context", "includeDeclaration"] params >>= asBool)
      o = docOutline d
      found =
        sortOn fst $
          [(refStart r, refEnd r) | r <- outlineReferences o, refName r == name]
            ++ [(declNameStart x, declNameEnd x) | withDecl, x <- outlineDeclarations o, declName x == name]
  pure (Array [location enc uri d a b | (a, b) <- nub found])

hover :: Handler
hover enc _ d params = do
  p <- member "position" params >>= locOf enc d
  (name, a, b) <- nameAt d p
  x <- find (\x -> declName x == name && declKind x == Annotation) (outlineDeclarations (docOutline d))
  pure $
    object
      [ ("contents", object [("kind", String "markdown"), ("value", String ("```peg\n" <> T.dropWhileEnd isSpace (declText x) <> "\n```"))])
      , ("range", rangeValue enc d a b)
      ]

documentSymbols :: Handler
documentSymbols enc _ d _ =
  let decls = outlineDeclarations (docOutline d)
      names = nub (map declName decls)
      symbol n = case [x | x <- decls, declName x == n] of
        [] -> Nothing
        xs@(first : _) ->
          let annotation = find ((== Annotation) . declKind) xs
           in Just . object $
                [ ("name", String n)
                , ("kind", int 12)
                , ("range", rangeValue enc d (minimum (map declStart xs)) (maximum (map declEnd xs)))
                , ("selectionRange", rangeValue enc d (declNameStart first) (declNameEnd first))
                ]
                  ++ [("detail", String (T.strip (T.drop 2 (snd (T.breakOn "::" (declText a)))))) | Just a <- [annotation]]
   in Just (Array (mapMaybe symbol names))
