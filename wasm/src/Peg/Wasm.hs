-- | The functions that the wasm reactor @peg-hs-wasm@ exports (ADR 0078):
-- each takes a request in JSON and returns a response in JSON.
--
-- 'analyzeJson' reads a grammar and generates its module in the steps of
-- @peg-hs gen@, and returns the diagnostics, the syntax tree of the
-- grammar as written, the generated types and the module. 'formatJson'
-- formats a grammar as @peg-hs fmt@ does. A request that is not JSON, has
-- no @grammar@ or has a member of another type gets only
-- @{\"error\": MESSAGE}@.
module Peg.Wasm
  ( analyzeJson
  , formatJson
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
import Peg.Grammar.Labels (labelWarnings)
import Peg.Grammar.Parser (parseGrammar, parseTops)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Peg.Grammar.Types (Classification (..), classify, dataTypeText)
import Peg.Lsp.Json
import System.FilePath (replaceExtension)

-- | Analyse a grammar. The request is
-- @{\"grammar\": TEXT, \"sourceName\": NAME, \"outputName\": NAME, \"debugEntry\": BOOL}@,
-- where only @grammar@ is required. @sourceName@ defaults to
-- @Grammar.hpeg@, @outputName@ to @sourceName@ with the extension @.hs@,
-- and @debugEntry@ to @false@, as the arguments of @peg-hs gen@. The
-- response is
-- @{\"diagnostics\": [...], \"ast\": NODE, \"types\": TEXT, \"module\": TEXT}@,
-- with @null@ for what the errors leave out.
analyzeJson :: Text -> Text
analyzeJson = respond $ \req -> do
  grammar <- grammarOf req
  source <- optional "sourceName" asText "a string" "Grammar.hpeg" req
  output <- optional "outputName" asText "a string" (T.pack (replaceExtension (T.unpack source) "hs")) req
  debug <- optional "debugEntry" asBool "a boolean" False req
  pure (analysis (Options (T.unpack source) (T.unpack output) debug Nothing) grammar)

-- | Format a grammar. The request is @{\"grammar\": TEXT}@, and the
-- response @{\"text\": TEXT, \"diagnostics\": [...]}@, whose @text@ is
-- @null@ when the grammar has errors.
formatJson :: Text -> Text
formatJson = respond $ \req -> do
  grammar <- grammarOf req
  pure $ case formatGrammar grammar of
    Left ds -> object [("text", Null), ("diagnostics", Array (map (diagnostic "error") ds))]
    Right t -> object [("text", String t), ("diagnostics", Array [])]

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

-- A member that may be left out.
optional :: Text -> (Value -> Maybe a) -> Text -> a -> Value -> Either Text a
optional name as what def req = case member name req of
  Nothing -> Right def
  Just v -> maybe (Left (name <> " is not " <> what)) Right (as v)

-- Analysis ------------------------------------------------------------------------

-- The steps of peg-hs gen (Command.Gen in peg-cli), keeping what each
-- step gives.
analysis :: Options -> Text -> Value
analysis opts src = case parseGrammar src of
  Left ds -> response ds [] Nothing Nothing Nothing
  Right g0 -> case expandTemplates g0 of
    Left ds -> response (templateNotes g0 ds) [] (Just g0) Nothing Nothing
    Right g -> case check g of
      Left ds -> response (templateNotes g0 ds) [] (Just g0) (Just g) Nothing
      Right _ ->
        let warnings = templateNotes g0 (labelWarnings g)
         in case generate opts g of
              Left ds -> response ds warnings (Just g0) (Just g) Nothing
              Right code -> response [] warnings (Just g0) (Just g) (Just code)
  where
    -- peg-hs gen writes the warnings before the errors of generate.
    response errors warnings parsed expanded code =
      object
        [ ("diagnostics", Array (map (diagnostic "warning") warnings ++ map (diagnostic "error") errors))
        , ("ast", maybe Null (grammarNode tops) parsed)
        , ("types", maybe Null (String . types) expanded)
        , ("module", maybe Null String code)
        ]
    tops = either (const []) id (parseTops src)

diagnostic :: Text -> Diagnostic -> Value
diagnostic severity (Diagnostic (Loc l c) m) =
  object [("severity", String severity), ("line", int l), ("column", int c), ("message", String m)]

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
  node "Grammar" (Just (Loc 1 1)) Nothing . map snd . sortOn fst $
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
