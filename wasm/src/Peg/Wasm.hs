-- | The functions that the wasm reactor @peg-hs-wasm@ exports (ADR 0078):
-- each takes a request in JSON and returns a response in JSON.
--
-- 'analyzeJson' reads a grammar and generates its module in the steps of
-- @peg-hs gen@, and returns the diagnostics, the syntax tree of the
-- grammar as written, the generated types and the module. 'formatJson'
-- formats a grammar as @peg-hs fmt@ does. 'parseInputJson' parses an input
-- with the interpreter of peg-grammar, without GHC (ADR 0090). A request
-- that is not JSON, has no @grammar@ or has a member of another type gets
-- only @{\"error\": MESSAGE}@.
module Peg.Wasm
  ( analyzeJson
  , formatJson
  , parseInputJson
  , errorJson
  ) where

import Data.Char (isSpace)
import Data.List (sortOn)
import Data.Maybe (fromMaybe, maybeToList)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Codegen (Options (..), generate)
import Peg.Grammar
import Peg.Grammar.Assemble (Top (..), advanceLoc)
import Peg.Grammar.Check (check)
import Peg.Grammar.Format (formatGrammar)
import Peg.Grammar.Import (resolveImports)
import Peg.Grammar.Interpret (interpret, interpreter, interpreterKindName)
import Peg.Grammar.Labels (labelWarnings)
import Peg.Grammar.Parser (parseGrammar, parseTops)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Peg.Grammar.Types (Classification (..), classify, dataTypeText)
import Peg.Lsp.Json
import Peg.Runtime (Expected (..), ParseError (..), Pos (..), renderParseError)
import Peg.Runtime.Syntax (SyntaxElement (..), SyntaxKind, SyntaxNode, syntaxChildrenWithTokens, syntaxKind, syntaxLabel, syntaxRange, tokenKind, tokenLabel, tokenRange, tokenText)
import qualified Data.Set as S
import System.FilePath (replaceExtension)

-- | Analyse a grammar. The request is
-- @{\"grammar\": TEXT, \"sourceName\": NAME, \"outputName\": NAME, \"debugEntry\": BOOL, \"imports\": {PATH: TEXT}}@,
-- where only @grammar@ is required. @sourceName@ defaults to
-- @Grammar.hpeg@, @outputName@ to @sourceName@ with the extension @.hs@,
-- and @debugEntry@ to @false@, as the arguments of @peg-hs gen@.
-- @imports@ has the texts of the libraries that the grammar imports, by
-- the paths of its @%import@s (ADR 0092), and defaults to @{}@; the
-- reactor reads no file. The response is
-- @{\"diagnostics\": [...], \"ast\": NODE, \"types\": TEXT, \"module\": TEXT}@,
-- with @null@ for what the errors leave out. The module is the one that
-- @peg-hs gen@ writes for the same grammar and libraries. A diagnostic in
-- a library has the path of its @%import@ as @file@.
analyzeJson :: Text -> Text
analyzeJson = respond $ \req -> do
  grammar <- grammarOf req
  source <- optional "sourceName" asText "a string" "Grammar.hpeg" req
  output <- optional "outputName" asText "a string" (T.pack (replaceExtension (T.unpack source) "hs")) req
  debug <- optional "debugEntry" asBool "a boolean" False req
  libraries <- importsOf req
  pure (analysis (Options (T.unpack source) (T.unpack output) debug Nothing) libraries grammar)

-- | Format a grammar. The request is @{\"grammar\": TEXT}@, and the
-- response @{\"text\": TEXT, \"diagnostics\": [...]}@, whose @text@ is
-- @null@ when the grammar has errors.
formatJson :: Text -> Text
formatJson = respond $ \req -> do
  grammar <- grammarOf req
  pure $ case formatGrammar grammar of
    Left ds -> object [("text", Null), ("diagnostics", Array (map (diagnostic [] "error") ds))]
    Right t -> object [("text", String t), ("diagnostics", Array [])]

-- | Parse an input with the interpreter (ADR 0090). The request is
-- @{\"grammar\": TEXT, \"input\": TEXT, \"entry\": NAME, \"imports\": {PATH: TEXT}}@,
-- where @entry@, a rule of @%entry@, may be left out or @null@ for the
-- start rule, and @imports@ has the texts of the libraries, as for
-- 'analyzeJson' (ADR 0092). The response is
-- @{\"diagnostics\": [...], \"accepted\": BOOL, \"parseError\": ERROR, \"tree\": NODE}@:
-- the diagnostics are the errors of the grammar, of the interpreter and
-- of an @entry@ that is not in @%entry@, in the form of 'analyzeJson';
-- @accepted@ is @null@ with them. The error of a rejected input is
-- @{\"line\", \"column\", \"offset\", \"expected\", \"label\", \"message\"}@,
-- with the line and the column from 1 (in code points), the offset in
-- bytes of UTF-8, what was expected as 'renderParseError' writes each one,
-- the label thrown or @null@, and the message of 'renderParseError'. A
-- node of the tree is
-- @{\"kind\", \"start\", \"end\", \"label\", \"text\", \"children\"}@, with
-- byte offsets; a token has its text and no children, and a node has
-- @null@ for its text.
parseInputJson :: Text -> Text
parseInputJson = respond $ \req -> do
  grammar <- grammarOf req
  input <- case member "input" req of
    Nothing -> Left "the request has no input"
    Just v -> maybe (Left "input is not a string") Right (asText v)
  entry <- optional "entry" (\v -> case v of Null -> Just Nothing; _ -> Just <$> asText v) "a string or null" Nothing req
  libraries <- importsOf req
  pure (interpreted libraries grammar input entry)

interpreted :: [(FilePath, Text)] -> Text -> Text -> Maybe Text -> Value
interpreted libraries src input entry = case parseGrammar src of
  Left ds -> failed [] ds
  Right root -> case resolveImports root libraries of
    Left ds -> failed (grammarImports root) ds
    Right g0 -> case expandTemplates g0 >>= \g -> (,) g <$> check g of
      Left ds -> failed (grammarImports g0) (templateNotes g0 ds)
      Right (g, an)
        | Just e <- entry, e `notElem` map unLoc (grammarEntries g) -> failed [] [Diagnostic (Loc 0 1 1) (e <> " is not a rule of %entry")]
        | otherwise -> case interpreter g an of
            Left ds -> failed (grammarImports g0) (templateNotes g0 ds)
            Right ip -> case interpret ip entry input of
              Left err -> result (Bool False) (parseErrorValue err) Null
              Right tree -> result (Bool True) Null (treeValue (interpreterKindName ip) tree)
  where
    failed imports ds = object [("diagnostics", Array (map (diagnostic imports "error") ds)), ("accepted", Null), ("parseError", Null), ("tree", Null)]
    result accepted err tree = object [("diagnostics", Array []), ("accepted", accepted), ("parseError", err), ("tree", tree)]

parseErrorValue :: ParseError -> Value
parseErrorValue e =
  object
    [ ("line", int (posLine p))
    , ("column", int (posColumn p))
    , ("offset", int (posOffset p))
    , ("expected", Array (map (String . expectedText) (S.toAscList (parseErrorExpected e))))
    , ("label", maybe Null String (parseErrorLabel e))
    , ("message", String (renderParseError e))
    ]
  where
    p = parseErrorPos e
    expectedText = \case
      ExpectedName t -> t
      ExpectedLiteral t -> t
      ExpectedClass t -> t
      ExpectedAny -> "any character"
      ExpectedEnd -> "end of input"

treeValue :: (SyntaxKind -> Text) -> SyntaxNode -> Value
treeValue name n =
  element (name (syntaxKind n)) (syntaxRange n) (syntaxLabel n) Null (map child (syntaxChildrenWithTokens n))
  where
    child = \case
      NodeElement c -> treeValue name c
      TokenElement t -> element (name (tokenKind t)) (tokenRange t) (tokenLabel t) (String (tokenText t)) []
    element kind (start, end) label text children =
      object
        [ ("kind", String kind)
        , ("start", int start)
        , ("end", int end)
        , ("label", maybe Null String label)
        , ("text", text)
        , ("children", Array children)
        ]

-- | The response @{\"error\": MESSAGE}@.
errorJson :: Text -> Text
errorJson m = renderJson (object [("error", String m)])

-- Requests ------------------------------------------------------------------------

respond :: (Value -> Either Text Value) -> Text -> Text
respond f t = case parseJson t of
  Nothing -> errorJson "the request is not JSON"
  Just req -> either errorJson renderJson (f req)

-- The grammar, without the byte order mark that peg-hs skips when it reads
-- a file.
grammarOf :: Value -> Either Text Text
grammarOf req = case member "grammar" req of
  Nothing -> Left "the request has no grammar"
  Just v -> maybe (Left "grammar is not a string") (Right . dropBom) (asText v)
  where
    dropBom g = fromMaybe g (T.stripPrefix "\xFEFF" g)

-- The texts of the libraries of a request (ADR 0092): the object of
-- @imports@, by path, or none without it.
importsOf :: Value -> Either Text [(FilePath, Text)]
importsOf req = case member "imports" req of
  Nothing -> Right []
  Just (Object kvs) -> mapM (\(k, v) -> maybe (Left "imports is not an object of strings") (\t -> Right (T.unpack k, dropBom t)) (asText v)) kvs
  Just _ -> Left "imports is not an object of strings"
  where
    dropBom t = fromMaybe t (T.stripPrefix "\xFEFF" t)

-- A member that may be left out.
optional :: Text -> (Value -> Maybe a) -> Text -> a -> Value -> Either Text a
optional name as what def req = case member name req of
  Nothing -> Right def
  Just v -> maybe (Left (name <> " is not " <> what)) Right (as v)

-- Analysis ------------------------------------------------------------------------

-- The steps of peg-hs gen (Command.Gen in peg-cli), keeping what each
-- step gives. The syntax tree is that of the grammar as written, without
-- the rules of its libraries.
analysis :: Options -> [(FilePath, Text)] -> Text -> Value
analysis opts libraries src = case parseGrammar src of
  Left ds -> response ds [] Nothing Nothing Nothing
  Right root -> case resolveImports root libraries of
    Left ds -> response ds [] (Just root) Nothing Nothing
    Right g0 -> case expandTemplates g0 of
      Left ds -> response (templateNotes g0 ds) [] (Just root) Nothing Nothing
      Right g -> case check g of
        Left ds -> response (templateNotes g0 ds) [] (Just root) (Just g) Nothing
        Right _ ->
          let warnings = templateNotes g0 (labelWarnings g)
           in case generate opts g of
                Left ds -> response ds warnings (Just root) (Just g) Nothing
                Right code -> response [] warnings (Just root) (Just g) (Just code)
  where
    -- peg-hs gen writes the warnings before the errors of generate.
    response errors warnings parsed expanded code =
      let imports = maybe [] grammarImports parsed
       in object
            [ ("diagnostics", Array (map (diagnostic imports "warning") warnings ++ map (diagnostic imports "error") errors))
            , ("ast", maybe Null (grammarNode tops) parsed)
            , ("types", maybe Null (String . types) expanded)
            , ("module", maybe Null String code)
            ]
    tops = either (const []) id (parseTops src)

-- A diagnostic, given the imports of the grammar; one in a library has the
-- path of its import as @file@ (ADR 0092).
diagnostic :: [Located FilePath] -> Text -> Diagnostic -> Value
diagnostic imports severity (Diagnostic (Loc f l c) m) =
  object ([("severity", String severity), ("line", int l), ("column", int c), ("message", String m)] ++ file)
  where
    file = case drop (f - 1) imports of
      Located _ p : _ | f > 0 -> [("file", String (T.pack p))]
      _ -> []

-- The declarations of the generated types, in the order of their rules.
types :: Grammar -> Text
types = T.intercalate "\n\n" . map dataTypeText . classDataTypes . classify

-- The syntax tree -----------------------------------------------------------------

node :: Text -> Maybe Loc -> Maybe Text -> [Value] -> Value
node kind loc text cs =
  object
    [ ("kind", String kind)
    , ("line", maybe Null (int . locLine) loc)
    , ("column", maybe Null (int . locColumn) loc)
    , ("text", maybe Null String text)
    , ("children", Array cs)
    ]

-- The grammar as parsed, its children in the order of their locations.
-- The directives come from the top-level items, which keep the locations
-- of both a directive and its argument; the grammar keeps one of the two,
-- and the values of %export and %language without their directive.
grammarNode :: [Top] -> Grammar -> Value
grammarNode tops g =
  node "Grammar" (Just (Loc 0 1 1)) Nothing . map snd . sortOn fst $
    [(l, directiveNode g l n al a) | TDirective l n al a <- tops]
      ++ [(l, node "Verbatim" (Just l) (Just t) []) | Located l t <- grammarVerbatim g]
      ++ [(ruleLoc r, ruleNode r) | r <- grammarRules g]

-- A directive at a location, with its name, and its argument at a location.
directiveNode :: Grammar -> Loc -> Text -> Loc -> Text -> Value
directiveNode g l name al a = node "Directive" (Just l) (Just ("%" <> name)) (map value values)
  where
    value (Located vl v) = node "Value" (Just vl) (Just v) []
    -- A directive and its argument are on one line.
    onLine = filter ((== locLine al) . locLine . locOf)
    values = case name of
      "syntax" -> []
      "export" -> onLine (grammarExports g)
      "language" -> onLine (grammarLanguages g)
      "deriving" -> maybe [] unLoc (grammarDeriving g)
      -- A label and a rule; a rule name or a label and a string as written,
      -- with its quotes (ADR 0089).
      _ | name `elem` ["recover", "expect", "message"] ->
        let (label, rest) = T.break isSpace a
            gap = T.takeWhile isSpace rest
         in [Located al label, Located (advanceLoc al (label <> gap)) (T.strip rest)]
      _ -> [Located al a]

ruleNode :: Rule -> Value
ruleNode r =
  node "Rule" (Just (ruleLoc r)) (Just (ruleName r)) $
    [node "Parameter" (Just (locOf (paramType p))) (Just (paramName p <> " :: " <> unLoc (paramType p))) [] | p <- ruleParams r]
      ++ [node "TemplateParameter" Nothing (Just (templateParam p)) [] | p <- ruleTemplateParams r]
      ++ [node "Type" (Just (locOf (ruleType r))) (Just (unLoc (ruleType r))) [] | Just _ <- [ruleAnnotation r]]
      ++ map altNode (ruleAlts r)
  where
    templateParam p = templateParamName p <> maybe "" (" :: " <>) (templateParamType p)

-- An alternative, its children in the order of their locations.
altNode :: Alt -> Value
altNode a =
  node "Alternative" (Just (altLoc a)) Nothing . map snd . sortOn fst $
    [(itemLoc i, itemNode i) | i <- altItems a]
      ++ [(l, node "Action" (Just l) (Just t) []) | Located l t <- maybeToList (altAction a)]
      ++ [(l, node "Constructor" (Just l) (Just t) []) | Located l t <- maybeToList (altConstructor a)]

itemNode :: Item -> Value
itemNode i = node "Item" (Just (itemLoc i)) (itemBind i) [exprNode (itemExpr i)]

argument :: Located Text -> Value
argument (Located l t) = node "Argument" (Just l) (Just t) []

exprNode :: Expr -> Value
exprNode = \case
  ELit _ written -> leaf "Literal" written
  EClass _ written -> leaf "Class" written
  EAny -> leaf "Any" "."
  ERef l name args -> node "Reference" (Just l) (Just name) (map argument args)
  EGroup seqs -> node "Group" Nothing Nothing [node "Sequence" Nothing Nothing (map itemNode s) | s <- seqs]
  EStar e -> unary "Star" e
  EPlus e -> unary "Plus" e
  EOpt e -> unary "Optional" e
  EAnd e -> unary "And" e
  ENot e -> unary "Not" e
  ECapture e -> unary "Capture" e
  EDiscard e -> unary "Discard" e
  ELabel l e label -> node "Label" (Just l) (Just label) [exprNode e]
  EPred positive (Located l code) -> node (if positive then "AndPredicate" else "NotPredicate") (Just l) (Just code) []
  ETemplate l name es args -> node "Template" (Just l) (Just name) (map exprNode es ++ map argument args)
  where
    leaf kind t = node kind Nothing (Just t) []
    unary kind e = node kind Nothing Nothing [exprNode e]
