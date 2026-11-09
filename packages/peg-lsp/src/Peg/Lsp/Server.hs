-- | The language server as a pure function from its state and a message to
-- the new state and the messages to send (ADR 0035).
--
-- The server supports diagnostics (pushed on @didOpen@ and @didChange@,
-- with incremental text synchronisation, ADR 0071), formatting, semantic tokens, go to
-- definition, references, hover, document symbols, and code actions that
-- insert safe labels and add recovery rules (ADR 0054) and write the
-- default constructor names of a rule (ADR 0075). Positions are
-- counted in UTF-16 code units, or in bytes when the client offers
-- @utf-8@ in @positionEncodings@.
--
-- Start from 'initialState' and pass each message to 'handleFrame' (for
-- the output of 'Peg.Lsp.Rpc.decodeFrames') or 'handleMessage' (for a
-- parsed message); send the messages of the t'Step' and stop when
-- 'stepExit' is set. A test can do it with values:
--
-- @
-- let open = object
--       [ (\"jsonrpc\", String \"2.0\"), (\"method\", String \"textDocument\/didOpen\")
--       , (\"params\", object [(\"textDocument\", object [(\"uri\", String \"file:\/\/\/a.hpeg\"), (\"text\", String src)])])
--       ]
--     s1 = handleMessage initialState (object [(\"jsonrpc\", String \"2.0\"), (\"id\", int 1), (\"method\", String \"initialize\"), (\"params\", object [])])
--     s2 = handleMessage (stepState s1) open
-- in stepOutput s2  -- [the textDocument\/publishDiagnostics notification]
-- @
--
-- A server reading a stream can coalesce the diagnostics of changes that
-- arrive faster than it checks them (ADR 0070): 'receiveFrame' and
-- 'receiveMessage' handle a message without computing the diagnostics of
-- a change, and 'publishPending' sends those of the latest version of each
-- changed document once no more input is waiting. "Peg.Lsp" does this over
-- handles. Requests are answered for the latest version either way.
--
-- Each version of a document is parsed by its top-level items, reusing the
-- results of the items that did not change ("Peg.Grammar.Incremental",
-- ADR 0071); the results are those of parsing the whole document.
--
-- A grammar with a @file:@ URI may import libraries (ADR 0092). The server
-- uses the text of an open library; for the others, the t'Step' of opening
-- or changing the grammar asks to read them ('stepReads'), and the caller
-- gives what it read to 'receiveFiles'. The diagnostics of a grammar wait
-- until its libraries are read. "Peg.Lsp" reads them with
-- 'Peg.Grammar.Import.Files.readLibrary'; a test gives the texts itself.
--
-- 'diagnose' is the analysis behind the diagnostics, usable on its own.
module Peg.Lsp.Server
  ( State
  , initialState
  , Step (..)
  , FileRequest (..)
  , receiveFiles
  , handleFrame
  , handleMessage
  , receiveFrame
  , receiveMessage
  , publishPending
  , Severity (..)
  , diagnose
  , tokenTypes
  , tokenModifiers
  , documentText
  , reparsedFragments
  ) where

import Data.Bits (shiftL, (.|.))
import qualified Data.ByteString as BS
import Data.Char (isSpace, ord)
import Data.List (find, nub, sortOn)
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Maybe (fromMaybe, isJust, listToMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Peg.Grammar (Diagnostic (..), Grammar (..), Loc (..), Located (Located))
import Peg.Grammar.Assemble (assemble, isIdentChar)
import Peg.Grammar.Check (check)
import Peg.Grammar.Constructors (constructorNameEdits)
import Peg.Grammar.Format (formatGrammar)
import Peg.Grammar.Assemble (Top)
import Peg.Grammar.Highlight
import Peg.Grammar.Incremental (Fragments, Parsed (..), noFragments, parseFragments)
import Peg.Grammar.Import (libraryErrors, resolveImports)
import Peg.Grammar.LabelInsertion (Edit (..), Insertion (..), RecoverProposal (..), insertLabelsWithImports, recoverProposalsWithImports)
import Peg.Grammar.Labels (labelWarnings)
import Peg.Grammar.Lint (LintLevel (..), LintWarning (..), lintGrammar)
import Peg.Grammar.Outline
import Peg.Grammar.Parser (parseTops)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Peg.Grammar.Types (Classification (..), Constructor (..), DataType (..), RuleType (..), constructorTypeText, dataTypeText, typeText)
import qualified Peg.Grammar.Types as Types
import Peg.Lsp.Json

-- | How positions count characters (LSP 3.17 @positionEncoding@).
data Encoding = Utf8 | Utf16
  deriving (Eq, Show)

data Document = Document
  { docText :: Text
  , docLines :: Seq.Seq Text
  -- ^ Indexed in logarithmic time: a diagnostic and a token look up their line.
  , docOutline :: Outline
  -- ^ Computed when first used, and kept until the document changes.
  , docChecks :: [(Severity, Diagnostic, Maybe Text)]
  -- ^ The diagnostics ('diagnose'), computed when first used, sharing the
  -- outline.
  , docLabels :: [Insertion]
  -- ^ The labels that can be inserted (ADR 0054), computed when first used.
  , docRecovers :: [RecoverProposal]
  -- ^ The recovery rules to propose (ADR 0054), computed when first used.
  , docTypes :: Maybe Classification
  -- ^ The types of the rules (ADR 0075), computed when first used; for a
  -- grammar that parses and whose templates expand.
  , docConstructors :: [(Text, [Edit])]
  -- ^ The edits that write the default constructor names of each rule
  -- (ADR 0075), computed when first used.
  , docFragments :: !Fragments
  -- ^ The parsed top-level fragments, for the next version (ADR 0071).
  , docParsed :: Int
  -- ^ How many fragments this version parsed, not found in the previous one.
  , docTops :: Either [Diagnostic] [Top]
  -- ^ The top-level items of the document.
  , docImports :: [Located FilePath]
  -- ^ The @%import@s of a grammar that parses (ADR 0092).
  , docLibraries :: [(FilePath, Text, Document)]
  -- ^ The libraries of the @%import@s whose texts the server has, by the
  -- path of the import, with their URIs (ADR 0092).
  }

-- | The libraries of a grammar (ADR 0092): the documents of those the
-- server has, by the path of the @%import@ and with their URIs, and the
-- errors of the others.
data Libraries = Libraries [(FilePath, Text, Document)] [Diagnostic]

-- | A file that the server asks to read (ADR 0092): a library that an open
-- grammar imports and that is not open, by its URI, the directory of the
-- grammar and the path of the @%import@. "Peg.Lsp" reads it with
-- 'Peg.Grammar.Import.Files.readLibrary' and gives the result to
-- 'receiveFiles'.
data FileRequest = FileRequest
  { requestUri :: Text
  , requestDirectory :: FilePath
  , requestPath :: FilePath
  }
  deriving (Eq, Show)

-- | The state of the server: the open documents, the position encoding
-- agreed on in @initialize@, and whether @initialize@ and @shutdown@ have
-- been received. Opaque; start from 'initialState'.
data State = State
  { stDocuments :: M.Map Text Document
  , stPending :: Set.Set Text
  -- ^ The documents changed since their diagnostics were last sent.
  , stEncoding :: Encoding
  , stInitialized :: Bool
  , stShutdown :: Bool
  , stFiles :: M.Map Text (Either Text Document)
  -- ^ The libraries read from the disk, by URI, or why they could not be
  -- read (ADR 0092).
  , stReading :: Set.Set Text
  -- ^ The URIs of the libraries asked to be read and not received yet.
  }

-- | The state before @initialize@: no document is open. Requests other
-- than @initialize@ are answered with an error until it arrives.
initialState :: State
initialState = State M.empty Set.empty Utf16 False False M.empty Set.empty

-- | The result of handling a message: the new state, the messages to send,
-- the exit status when the server must stop, and the files to read
-- (ADR 0092), whose contents go to 'receiveFiles'.
data Step = Step
  { stepState :: State
  , stepOutput :: [Value]
  , stepExit :: Maybe Int
  , stepReads :: [FileRequest]
  }

-- A step that reads no file.
plain :: State -> [Value] -> Maybe Int -> Step
plain st out code = Step st out code []

-- | Handle the body of a framed message, or an error of the framing (see
-- 'Peg.Lsp.Rpc.decodeFrames'). A framing error or a body that is not JSON
-- is answered with a parse error (-32700).
handleFrame :: State -> Either Text Text -> Step
handleFrame st = withPublish . receiveFrame st

-- | Handle a parsed message: a request (with an @id@), which gets a
-- response, or a notification. A message without a method is ignored.
-- The diagnostics of a document that the message opens or changes are
-- sent with it.
handleMessage :: State -> Value -> Step
handleMessage st = withPublish . receiveMessage st

-- Send the pending diagnostics after the messages of a step, unless the
-- server stops.
withPublish :: Step -> Step
withPublish step = case stepExit step of
  Just _ -> step
  Nothing ->
    let p = publishPending (stepState step)
     in p {stepOutput = stepOutput step ++ stepOutput p, stepReads = stepReads step}

-- | 'handleFrame' without the diagnostics of the document that the message
-- opens or changes: they wait for 'publishPending' (ADR 0070).
receiveFrame :: State -> Either Text Text -> Step
receiveFrame st = \case
  Left err -> plain st [errorResponse Null (-32700) err] Nothing
  Right body -> case parseJson body of
    Nothing -> plain st [errorResponse Null (-32700) "the message is not JSON"] Nothing
    Just v -> receiveMessage st v

-- | 'handleMessage' without the diagnostics of the document that the
-- message opens or changes: they wait for 'publishPending' (ADR 0070),
-- or for @shutdown@, which sends them before its response. Requests are
-- answered for the latest version of the document.
receiveMessage :: State -> Value -> Step
receiveMessage st msg =
  case (member "method" msg >>= asText, member "id" msg) of
    (Nothing, _) -> plain st [] Nothing
    (Just m, Just i) -> request st m i params
    (Just m, Nothing) -> notification st m params
  where
    params = fromMaybe Null (member "params" msg)

request :: State -> Text -> Value -> Value -> Step
request st method i params
  | method == "initialize" =
      let enc = if any (== String "utf-8") (fromMaybe [] (path ["capabilities", "general", "positionEncodings"] params >>= asArray)) then Utf8 else Utf16
       in plain st {stEncoding = enc, stInitialized = True} [response i (initializeResult enc)] Nothing
  | not (stInitialized st) = plain st [errorResponse i (-32002) "the server is not initialized"] Nothing
  | stShutdown st = plain st [errorResponse i (-32600) "the server is shutting down"] Nothing
  -- The diagnostics still waiting are sent before the server shuts down.
  | method == "shutdown" =
      let p = publishPending st
       in plain (stepState p) {stShutdown = True} (stepOutput p ++ [response i Null]) Nothing
  | otherwise = case lookup method handlers of
      Just h -> plain st [response i (fromMaybe Null (document >>= \(uri, d) -> h (stEncoding st) uri d params))] Nothing
      Nothing -> plain st [errorResponse i (-32601) ("unknown method " <> method)] Nothing
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
      , ("textDocument/codeAction", codeActions)
      ]

notification :: State -> Text -> Value -> Step
notification st method params = case method of
  "exit" -> plain st [] (Just (if stShutdown st then 0 else 1))
  "textDocument/didOpen"
    | Just uri <- path ["textDocument", "uri"] params >>= asText
    , Just text <- path ["textDocument", "text"] params >>= asText ->
        open uri noFragments text
  -- Changes of ranges or of the full text, applied in order (ADR 0071).
  "textDocument/didChange"
    | Just uri <- path ["textDocument", "uri"] params >>= asText
    , Just changes <- member "contentChanges" params >>= asArray ->
        let d = M.lookup uri (stDocuments st)
         in open uri (maybe noFragments docFragments d) (foldl (applyChange (stEncoding st)) (maybe "" docText d) changes)
  -- A grammar that imports a closed library reads it from the disk again.
  "textDocument/didClose"
    | Just uri <- path ["textDocument", "uri"] params >>= asText ->
        let st1 = st {stDocuments = M.delete uri (stDocuments st), stPending = Set.delete uri (stPending st)}
            requests = [r | u <- importers st1 uri, Just d <- [M.lookup u (stDocuments st1)], r <- fileRequests st1 u d, requestUri r == uri]
            st2 = st1 {stReading = Set.union (stReading st1) (Set.fromList (map requestUri requests))}
         in Step (refresh (Set.fromList (importers st2 uri)) st2) [publish uri []] Nothing (take 1 requests)
  _ -> plain st [] Nothing
  where
    -- The libraries of the grammar that are not open are read again
    -- (ADR 0092), and the grammars that import the document are checked
    -- again with its text.
    open uri table text =
      let d = newDocument table text
          st1 = st {stDocuments = M.insert uri d (stDocuments st)}
          requests = fileRequests st1 uri d
          st2 = st1 {stReading = Set.union (stReading st1) (Set.fromList (map requestUri requests))}
       in Step (refresh (Set.fromList (uri : importers st2 uri)) st2) [] Nothing requests

-- | Give the server the files that it asked to read (ADR 0092), by URI:
-- the text of each, or why it could not be read, such as
-- @no such file@. The grammars that import them are checked again, and
-- their diagnostics wait for 'publishPending'.
receiveFiles :: State -> [(Text, Either Text Text)] -> Step
receiveFiles st files =
  let uris = map fst files
      st1 =
        st
          { stFiles = foldl (\m (u, r) -> M.insert u (newDocument noFragments <$> r) m) (stFiles st) files
          , stReading = Set.difference (stReading st) (Set.fromList uris)
          }
   in plain (refresh (Set.fromList (concatMap (importers st1) uris)) st1) [] Nothing

-- The files to read for the imports of a document: the libraries that are
-- not open, of a grammar whose URI is a file.
fileRequests :: State -> Text -> Document -> [FileRequest]
fileRequests st uri d = case uriDirectory uri of
  Nothing -> []
  Just dir ->
    [ FileRequest u dir p
    | Located _ p <- docImports d
    , let u = libraryUri uri p
    , not (M.member u (stDocuments st))
    ]

-- The open documents that import a URI.
importers :: State -> Text -> [Text]
importers st uri = [u | (u, d) <- M.toList (stDocuments st), uri `elem` [libraryUri u p | Located _ p <- docImports d]]

-- The documents of the URIs given analysed again with the libraries the
-- server has, and their diagnostics pending.
refresh :: Set.Set Text -> State -> State
refresh uris st =
  st
    { stDocuments = M.mapWithKey (\u d -> if Set.member u uris then analysed (librariesOf st u d) d else d) (stDocuments st)
    , stPending = Set.union (stPending st) (Set.intersection uris (M.keysSet (stDocuments st)))
    }

-- The libraries of a document that the server has: open, or read from the
-- disk (ADR 0092). The @%import@s of a grammar whose URI is not a file are
-- errors.
librariesOf :: State -> Text -> Document -> Libraries
librariesOf st uri d = case (docImports d, uriDirectory uri) of
  ([], _) -> Libraries [] []
  (imports, Nothing) -> Libraries [] [Diagnostic l "imports need a file: save the grammar first" | Located l _ <- imports]
  (imports, Just _) ->
    let found = [(i, u, M.lookup u (stDocuments st), M.lookup u (stFiles st)) | i@(Located _ p) <- imports, let u = libraryUri uri p]
     in Libraries
          [(p, u, doc) | (Located _ p, u, opened, file) <- found, Just doc <- [maybe (file >>= either (const Nothing) Just) Just opened]]
          [Diagnostic l ("cannot import " <> T.pack p <> ": " <> reason) | (Located l p, _, Nothing, Just (Left reason)) <- found]

-- | The URI of a library, given the URI of the grammar and the path of its
-- @%import@ (ADR 0092): the path joined to the directory of the URI.
libraryUri :: Text -> FilePath -> Text
libraryUri uri p = fst (T.breakOnEnd "/" uri) <> T.pack p

-- The directory of a @file:@ URI, as a path of the file system: the path
-- of the URI without its last part, percent-decoded. A drive letter of
-- Windows (@file:///c%3A/x.hpeg@) loses the slash before it.
uriDirectory :: Text -> Maybe FilePath
uriDirectory uri = do
  rest <- T.stripPrefix "file://" uri
  let (_, pathPart) = T.breakOn "/" rest
      dir = T.dropEnd 1 (fst (T.breakOnEnd "/" pathPart))
  decoded <- percentDecode dir
  pure $ case T.unpack decoded of
    '/' : d : ':' : more | d `elem` (['a' .. 'z'] ++ ['A' .. 'Z']) -> d : ':' : more
    s -> if null s then "/" else s

-- Decode the escapes %XX of a URI as UTF-8.
percentDecode :: Text -> Maybe Text
percentDecode t = either (const Nothing) Just . TE.decodeUtf8' . BS.pack =<< go (BS.unpack (TE.encodeUtf8 t))
  where
    go = \case
      [] -> Just []
      37 : a : b : rest -> (:) <$> ((\x y -> x * 16 + y) <$> hex a <*> hex b) <*> go rest
      37 : _ -> Nothing
      c : rest -> (c :) <$> go rest
    hex c
      | c >= 48 && c <= 57 = Just (c - 48)
      | c >= 65 && c <= 70 = Just (c - 55)
      | c >= 97 && c <= 102 = Just (c - 87)
      | otherwise = Nothing

-- | Send the diagnostics of the latest version of each document opened or
-- changed since they were last sent, in the order of their URIs. Those of
-- a grammar that waits for a library to be read (ADR 0092) wait for it.
publishPending :: State -> Step
publishPending st =
  plain
    st {stPending = waiting}
    [ publish uri (map (diagnosticValue (stEncoding st) d) (docChecks d))
    | uri <- Set.toAscList (Set.difference (stPending st) waiting)
    , Just d <- [M.lookup uri (stDocuments st)]
    ]
    Nothing
  where
    waiting =
      Set.filter
        (\u -> maybe False (\d -> any (\(Located _ p) -> Set.member (libraryUri u p) (stReading st)) (docImports d)) (M.lookup u (stDocuments st)))
        (stPending st)

-- A version of a document, parsed with the fragments of the previous one,
-- and analysed without libraries.
newDocument :: Fragments -> Text -> Document
newDocument table text =
  let p = parseFragments table text
      o = parsedOutline p
      tops = parsedTops p
   in analysed (Libraries [] []) $
        Document
          { docText = text
          , docLines = Seq.fromList (T.splitOn "\n" text)
          , docOutline = o
          , docChecks = []
          , docLabels = []
          , docRecovers = []
          , docTypes = Nothing
          , docConstructors = constructorNameEdits text
          , docFragments = parsedFragments p
          , docParsed = parsedNew p
          , docTops = tops
          , docImports = either (const []) (\g -> if isJust (grammarLibrary g) then [] else grammarImports g) (tops >>= assemble)
          , docLibraries = []
          }

-- A document analysed with the libraries it imports (ADR 0092).
analysed :: Libraries -> Document -> Document
analysed libs@(Libraries docs _) d =
  d
    { docChecks = diagnoseWith libs (docOutline d) (docTops d)
    , docLabels = either (const []) fst (insertLabelsWithImports texts [] (docText d))
    , docRecovers = either (const []) id (recoverProposalsWithImports texts (docText d))
    , docTypes = either (const Nothing) (Just . Types.classify) (docTops d >>= assemble >>= \g -> resolveImports g texts >>= expandTemplates)
    , docLibraries = docs
    }
  where
    texts = [(p, docText x) | (p, _, x) <- docs]


-- | The text of an open document. For tests.
documentText :: State -> Text -> Maybe Text
documentText st uri = docText <$> M.lookup uri (stDocuments st)

-- | How many top-level fragments the latest version of an open document
-- parsed, not found in the previous version (ADR 0071). For tests.
reparsedFragments :: State -> Text -> Maybe Int
reparsedFragments st uri = docParsed <$> M.lookup uri (stDocuments st)

-- Apply a change of @didChange@: the full text, or a range and its text.
-- A position past the end of a line is the end of the line, and a line
-- past the end of the document the end of the document (LSP 3.17).
applyChange :: Encoding -> Text -> Value -> Text
applyChange enc text c = fromMaybe text $ do
  new <- member "text" c >>= asText
  case member "range" c of
    Nothing -> pure new
    Just r -> do
      a <- member "start" r >>= offsetOf
      b <- member "end" r >>= offsetOf
      pure (T.take a text <> new <> T.drop (max a b) text)
  where
    ls = T.splitOn "\n" text
    offsetOf v = do
      line <- member "line" v >>= asInt
      ch <- member "character" v >>= asInt
      pure $ case drop (max 0 line) ls of
        [] -> T.length text
        l : _ ->
          let go k n t = case T.uncons t of
                Just (x, rest) | n + units enc (T.singleton x) <= ch -> go (k + 1) (n + units enc (T.singleton x)) rest
                _ -> k
           in sum (map ((+ 1) . T.length) (take (max 0 line) ls)) + go 0 0 (fromMaybe l (T.stripSuffix "\r" l))

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
          , ("textDocumentSync", object [("openClose", Bool True), ("change", int 2)])
          , ("documentFormattingProvider", Bool True)
          , ("semanticTokensProvider", object [("legend", object [("tokenTypes", Array (map String tokenTypes)), ("tokenModifiers", Array (map String tokenModifiers))]), ("full", Bool True)])
          , ("definitionProvider", Bool True)
          , ("referencesProvider", Bool True)
          , ("hoverProvider", Bool True)
          , ("documentSymbolProvider", Bool True)
          , ("codeActionProvider", Bool True)
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
  | -- | An info of @peg-hs lint@ (ADR 0063, ADR 0067). Editors show hints
    -- faintly, often without an underline.
    Hint
  deriving (Eq, Show)

-- | The diagnostics of a grammar with the messages and locations of
-- @peg-hs gen@ and @peg-hs lint@, and the code of a lint rule
-- ('Peg.Grammar.Lint.lintRule'). An error stops the checks as in
-- @peg-hs gen@: a grammar with an error has no warnings. The warnings of
-- the linter have the severity 'Warning', and its infos 'Hint'.
-- A grammar with a syntax error has only its syntax errors: the first is the one of
-- @peg-hs gen@, followed by those that recovery finds on later lines.
--
-- A library (ADR 0092) is checked on its own. A grammar that imports
-- libraries is not given them here, so its @%import@s are errors
-- (@cannot import lex\/Ident.hpeg: no such file@); the server checks it
-- with the libraries.
diagnose :: Text -> [(Severity, Diagnostic, Maybe Text)]
diagnose src = diagnoseWith (Libraries [] []) (outline src) (parseTops src)

-- 'diagnose' with the libraries of the grammar, from the outline of the
-- text, which only a grammar with a syntax error needs, and its top-level
-- items. The diagnostics located in a library are at its @%import@, with
-- the path, line and column in the library before the message
-- (ADR 0092). The warnings of the linter in the libraries are left to the
-- libraries themselves.
diagnoseWith :: Libraries -> Outline -> Either [Diagnostic] [Top] -> [(Severity, Diagnostic, Maybe Text)]
diagnoseWith (Libraries docs importErrors) o parsed = case parsed of
  Left ds@(d : _) ->
    map (\x -> (Error, x, Nothing)) ds
      ++ [(Error, e, Nothing) | e <- outlineSyntaxErrors o, locLine (diagLoc e) > locLine (diagLoc d)]
  Left [] -> []
  Right tops -> case assemble tops of
    Left ds -> errors ds
    Right g0
      | isJust (grammarLibrary g0) -> case libraryErrors g0 of
          [] -> lints (lintGrammar g0)
          ds -> errors ds
      | not (null importErrors) -> errors importErrors
      | otherwise -> case resolveImports g0 texts >>= \g1 -> either (Left . templateNotes g1) (Right . (,) g1) (expandTemplates g1 >>= \g -> g <$ check g) of
          Left ds -> errors (map (atImport g0) ds)
          Right (g1, g) ->
            [(Warning, atImport g0 w, Nothing) | w <- templateNotes g1 (labelWarnings g)]
              ++ lints (filter ((== 0) . locFile . lintLoc) (lintGrammar g1))
  where
    texts = [(p, docText x) | (p, _, x) <- docs]
    errors = map (\x -> (Error, x, Nothing))
    lints ws = [(severity (lintLevel w), Diagnostic (lintLoc w) (lintMessage w <> " [" <> lintRule w <> "]; " <> lintHint w), Just (lintRule w)) | w <- ws]
    severity LevelWarning = Warning
    severity LevelInfo = Hint
    -- A diagnostic in a library, at the %import of the library.
    atImport g0 x@(Diagnostic (Loc f l c) m) = case drop (f - 1) (grammarImports g0) of
      Located il p : _ | f > 0 -> Diagnostic il (T.pack p <> ":" <> T.pack (show l) <> ":" <> T.pack (show c) <> ": " <> m)
      _ -> x


diagnosticValue :: Encoding -> Document -> (Severity, Diagnostic, Maybe Text) -> Value
diagnosticValue enc d (sev, Diagnostic l@(Loc _ line col) msg, code) =
  object $
    [ ("range", rangeValue enc d l (Loc 0 line (col + max 1 (T.length (T.takeWhile isIdentChar (T.drop (col - 1) (lineAt d line)))))))
    , ("severity", int (case sev of Error -> 1; Warning -> 2; Hint -> 4))
    , ("source", String "peg-hs")
    , ("message", String msg)
    ]
      ++ [("code", String c) | Just c <- [code]]

-- Positions -----------------------------------------------------------------------

lineAt :: Document -> Int -> Text
lineAt d n = fromMaybe "" (Seq.lookup (n - 1) (docLines d))

units :: Encoding -> Text -> Int
units Utf8 t = BS.length (TE.encodeUtf8 t)
units Utf16 t = T.foldl' (\n c -> n + if ord c > 0xFFFF then 2 else 1) 0 t

positionValue :: Encoding -> Document -> Loc -> Value
positionValue enc d (Loc _ l c) = object [("line", int (l - 1)), ("character", int (units enc (T.take (c - 1) (lineAt d l))))]

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
  pure (Loc 0 (line + 1) (go 1 0 text))

within :: Loc -> Loc -> Loc -> Bool
within p a b = a <= p && p <= b

-- Features ------------------------------------------------------------------------

type Handler = Encoding -> Text -> Document -> Value -> Maybe Value

formatting :: Handler
formatting enc _ d _ = Just $ case formatGrammar (docText d) of
  Right out
    | out /= docText d ->
        let lastLine = Seq.length (docLines d)
            end = Loc 0 lastLine (T.length (lineAt d lastLine) + 1)
         in Array [object [("range", rangeValue enc d (Loc 0 1 1) end), ("newText", String out)]]
  _ -> Array []

-- | The token types of the semantic tokens, in the order of their indices,
-- as announced in the legend of the @initialize@ response.
tokenTypes :: [Text]
tokenTypes = ["function", "macro", "parameter", "variable", "string", "regexp", "keyword", "operator", "decorator", "comment", "namespace", "enumMember", "type"]

-- | The token modifiers, in the order of their bits.
tokenModifiers :: [Text]
tokenModifiers = ["declaration", "definition", "defaultLibrary"]

semanticTokens :: Handler
semanticTokens enc _ d _ =
  let o = docOutline d
      tokens = sortOn (\(a, _, _, _) -> a) (mapMaybe (classify o) (outlineHighlights o))
      encoded = go (Loc 0 1 1) tokens
      go _ [] = []
      go (Loc _ pl pc) ((a@(Loc _ l c), Loc _ _ ec, ty, mods) : rest) =
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
  HBinding -> Just (start, Loc 0 (locLine end) (locColumn end - 1), "variable", ["declaration"])
  HReservedBinding -> Just (start, end, "variable", ["defaultLibrary"])
  HLiteral -> Just (start, end, "string", [])
  HClass -> Just (start, end, "regexp", [])
  HDirective -> Just (start, end, "keyword", [])
  HOperator -> Just (start, end, "operator", [])
  HChoice -> Just (start, end, "operator", [])
  HDefinition -> Just (start, end, "operator", [])
  HLabel -> Just (start, end, "decorator", [])
  HDirectiveRule -> Just (start, end, "function", [])
  HDirectiveLabel -> Just (start, end, "decorator", [])
  HModuleName -> Just (start, end, "namespace", [])
  HConstructor -> Just (start, end, "enumMember", [])
  HClassName -> Just (start, end, "type", [])
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

-- The definition of a rule of the document, or else of a library that it
-- imports (ADR 0092), in the document of the library.
definition :: Handler
definition enc uri d params = do
  p <- member "position" params >>= locOf enc d
  (name, _, _) <- nameAt d p
  (u, doc, decls) <- declarationsOf uri d name
  x <- listToMaybe ([x | x <- decls, declKind x == Definition] ++ decls)
  pure (location enc u doc (declNameStart x) (declNameEnd x))

-- The declarations of a rule in a document, or else in the first library
-- that has them, with the URI and the document where they are.
declarationsOf :: Text -> Document -> Text -> Maybe (Text, Document, [Declaration])
declarationsOf uri d name =
  listToMaybe
    [ (u, doc, decls)
    | (u, doc) <- (uri, d) : [(lu, ld) | (_, lu, ld) <- docLibraries d]
    , let decls = [x | x <- outlineDeclarations (docOutline doc), declName x == name]
    , not (null decls)
    ]

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
  constructorHover p `orElse` ruleHover p
  where
    orElse (Just x) _ = Just x
    orElse Nothing y = y
    contents a b value =
      object
        [ ("contents", object [("kind", String "markdown"), ("value", String value)])
        , ("range", rangeValue enc d a b)
        ]
    -- The type of the constructor of @Name (ADR 0075).
    constructorHover p = do
      h <- find (\x -> hlKind x == HConstructor && within p (hlStart x) (hlEnd x)) (outlineHighlights (docOutline d))
      types <- docTypes d
      (dt, c) <- find (\(_, c) -> conNameLoc c == Just (hlStart h)) [(dt, c) | dt <- classDataTypes types, c <- dataConstructors dt]
      pure (contents (hlStart h) (hlEnd h) ("```haskell\n" <> constructorTypeText dt c <> "\n```"))
    ruleHover p = do
      (name, a, b) <- nameAt d p
      let decls = maybe [] (\(_, _, xs) -> xs) (declarationsOf "" d name)

      -- A rule without a type annotation has type () (ADR 0066), unless
      -- its type is inferred or generated (ADR 0075).
      value <- case (find ((== Annotation) . declKind) decls, find ((== Definition) . declKind) decls) of
        (Just x, _) -> Just (peg (T.dropWhileEnd isSpace (declText x)))
        (Nothing, Just _) -> case docTypes d >>= \c -> if Set.member name (classUnknown c) then Nothing else M.lookup name (classRules c) of
          Just (Inferred t) -> Just (peg (name <> " :: " <> typeText t))
          Just (Generated dt) -> Just (peg (name <> " :: " <> dataName dt) <> "\n\n```haskell\n" <> dataTypeText dt <> "\n```")
          Just UnitType -> Just (peg (name <> " :: ()"))
          _ -> Nothing
        _ -> Nothing
      pure (contents a b value)
    peg t = "```peg\n" <> t <> "\n```"

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

-- The code actions of ADR 0054: a label at a position where the label check
-- shows it to be safe, all those labels, and @%recover@ with a recovery
-- rule for a label without one.
codeActions :: Handler
codeActions enc uri d params = do
  a <- path ["range", "start"] params >>= locOf enc d
  b <- path ["range", "end"] params >>= locOf enc d
  let overlaps s e = s <= b && a <= e
      labelEdit i = Edit (insertionEnd i) (" ^" <> insertionName i)
      labels = docLabels d
  pure . Array $
    [action ("Add the label ^" <> insertionName i) [labelEdit i] | i <- labels, overlaps (insertionStart i) (insertionEnd i)]
      ++ [action ("Add the " <> T.pack (show (length labels)) <> " labels that are safe") (map labelEdit labels) | not (null labels)]
      ++ [ action ("Add %recover " <> proposalLabel p <> " and the rule " <> proposalRule p) (proposalEdits p)
         | p <- docRecovers d
         , overlaps (proposalStart p) (proposalEnd p)
         ]
      -- ADR 0075
      ++ [ action ("Write the constructor names of rule " <> rule) edits
         | (rule, edits) <- docConstructors d
         , any (\x -> declName x == rule && declKind x == Definition && overlaps (declStart x) (declEnd x)) (outlineDeclarations (docOutline d))
         ]
  where
    action title edits =
      object
        [ ("title", String title)
        , ("kind", String "refactor.rewrite")
        , ("edit", object [("changes", object [(uri, Array [textEdit e | e <- edits])])])
        ]
    textEdit (Edit at text) = object [("range", rangeValue enc d at at), ("newText", String text)]
