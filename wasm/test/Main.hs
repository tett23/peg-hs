-- | Tests of the JSON functions of the wasm reactor (ADR 0078).
module Main (main) where

import Control.Monad (forM_)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.List (sort)
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Format (formatGrammar)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Lsp.Json
import Peg.Wasm (analyzeJson, formatJson)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist, listDirectory)
import System.Exit (ExitCode (..))
import System.FilePath (takeBaseName, takeDirectory, takeExtension, (</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode)
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit

main :: IO ()
main = do
  conformance <- grammarsUnder "../conformance" [".hpeg"]
  fixtures <- (++) <$> grammarsUnder "../packages/peg-codegen/test/fixtures" [".hpeg"] <*> grammarsUnder "../packages/peg-codegen/test/explicit" [".txt"]
  defaultMain $
    testGroup
      "peg-wasm"
      [ analyzeTests
      , testGroup "the module is the one of peg-hs gen" [genTest f d | f <- conformance ++ fixtures, d <- [False, True]]
      , testGroup "the names of the files" nameTests
      , astTests conformance
      , formatTests conformance
      , requestTests
      , auditFixTests
      ]

-- The grammar files under a directory, without the test data of the
-- conformance tests.
grammarsUnder :: FilePath -> [String] -> IO [FilePath]
grammarsUnder dir exts = do
  entries <- sort <$> listDirectory dir
  concat
    <$> mapM
      ( \e -> do
          let p = dir </> e
          isDir <- doesDirectoryExist p
          if isDir
            then if e == "data" then pure [] else grammarsUnder p exts
            else pure [p | takeExtension p `elem` exts]
      )
      entries

-- Requests and responses ----------------------------------------------------------

analyze :: [(Text, Value)] -> Value
analyze ms = response (analyzeJson (renderJson (object ms)))

format :: Text -> Value
format g = response (formatJson (renderJson (object [("grammar", String g)])))

response :: Text -> Value
response t = fromMaybe (error ("not JSON: " <> T.unpack t)) (parseJson t)

analyzeGrammar :: Text -> Value
analyzeGrammar g = analyze [("grammar", String g)]

field :: Text -> Value -> Value
field k v = fromMaybe (error ("no member " <> T.unpack k <> " in " <> T.unpack (renderJson v))) (member k v)

diagnostics :: Value -> [Value]
diagnostics = fromMaybe [] . asArray . field "diagnostics"

-- A diagnostic as (severity, line, column, message).
diagnostic :: Value -> (Text, Int, Int, Text)
diagnostic d =
  ( fromMaybe "" (member "severity" d >>= asText)
  , fromMaybe 0 (member "line" d >>= asInt)
  , fromMaybe 0 (member "column" d >>= asInt)
  , fromMaybe "" (member "message" d >>= asText)
  )

textOf :: Text -> Value -> Text
textOf k v = fromMaybe (error ("member " <> T.unpack k <> " is not a string: " <> T.unpack (renderJson v))) (asText (field k v))

-- The README grammar whose types are generated (ADR 0075).
calcGenerated :: Text
calcGenerated =
  T.unlines
    [ "%module Calc.Generated"
    , ""
    , "Expr <- Expr '+' Sp Term @Add"
    , "     / Term"
    , ""
    , "Term <- Term '*' Sp Atom @Mul"
    , "     / Atom"
    , ""
    , "Atom <- Num"
    , "     / '(' Sp Expr ')' Sp"
    , ""
    , "Num <- $[0-9]+ Sp"
    , ""
    , "Sp <- ' '*"
    ]

analyzeTests :: TestTree
analyzeTests =
  testGroup
    "analyze"
    [ testCase "JsonGenerated.hpeg has no diagnostics and generates data Value" $ do
        src <- TIO.readFile "../conformance/bench/JsonGenerated.hpeg"
        let r = analyzeGrammar src
        diagnostics r @?= []
        assertBool "types has data Value" ("data Value" `T.isInfixOf` textOf "types" r)
        assertBool "a module" (isJust (asText (field "module" r)))
    , testCase "the README grammar generates data Expr" $ do
        let r = analyzeGrammar calcGenerated
        diagnostics r @?= []
        assertBool "types has data Expr" ("data Expr = Add Expr Term | Expr2 Term" `T.isInfixOf` textOf "types" r)
        -- The types are joined by blank lines.
        assertBool "a blank line between types" ("  deriving (Eq, Show)\n\ndata Term" `T.isInfixOf` textOf "types" r)
    , testCase "an undefined rule is an error at the reference" $ do
        let r = analyzeGrammar "%module A\n\nS <- 'a' T\n"
        map diagnostic (diagnostics r) @?= [("error", 3, 10, "undefined rule T")]
        assertBool "an ast" (field "ast" r /= Null)
        assertBool "types" (field "types" r /= Null)
        field "module" r @?= Null
    , testCase "a syntax error has no ast, types or module" $ do
        let r = analyzeGrammar "%module A\n\nS <- ('a'\n"
        field "ast" r @?= Null
        field "types" r @?= Null
        field "module" r @?= Null
        case map diagnostic (diagnostics r) of
          [("error", l, c, m)] -> assertBool "a location and a message" (l > 0 && c > 0 && not (T.null m))
          ds -> assertFailure ("one error expected: " <> show ds)
    , testCase "a label that may reject valid input is a warning, and the module is generated" $ do
        let r = analyzeGrammar "%module A\nS <- 'a' ('b' ^l) { () } / 'a' 'c' { () }\n"
        map diagnostic (diagnostics r) @?= [("warning", 2, 11, "the label l may reject valid input: where it fails, the alternative at 2:28 can match")]
        assertBool "a module" (isJust (asText (field "module" r)))
    , testCase "an error of a template body notes the call" $ do
        let r = analyzeGrammar "%module A\n\nS <- T<'a'>\n\nT<p> :: ()\nT<p> <- p U\n"
        case map diagnostic (diagnostics r) of
          [("error", _, _, m)] -> assertBool (T.unpack m) ("undefined rule U" `T.isInfixOf` m && "3:6" `T.isInfixOf` m)
          ds -> assertFailure ("one error expected: " <> show ds)
        field "module" r @?= Null
    , testCase "a predicate that refers to a binding on its right is an error at the name (ADR 0082)" $ do
        let r = analyzeGrammar "%module A\nS :: Int\nS <- &{ y > 0 } y:N { y }\nN :: Int\nN <- [0-9] { 1 }\n"
        map diagnostic (diagnostics r) @?= [("error", 3, 9, "the predicate refers to y, which is bound to its right")]
        field "module" r @?= Null
    , testCase "an empty types for a grammar without generated types" $ do
        let r = analyzeGrammar "%module A\nS <- 'a'\n"
        textOf "types" r @?= ""
    , testCase "non-ASCII names and comments come back as written" $ do
        let src = "%module A\n\n# 数式の文法\n数式 <- 項 ('+' 項)*\n\n項 <- [0-9]+\n"
            r = analyzeGrammar src
        diagnostics r @?= []
        map (textOf "text") (filter ((== String "Rule") . field "kind") (children (field "ast" r))) @?= ["数式", "項"]
        let f = format src
        textOf "text" f @?= either (const "") id (formatGrammar src)
        assertBool "the comment" ("# 数式の文法" `T.isInfixOf` textOf "text" f)
        assertBool "the rule in the module" ("数式" `T.isInfixOf` textOf "module" r)
    , testCase "a column counts code points, a tab as one" $ do
        let r = analyzeGrammar "%module A\n\n数式 <-\t'a' T\n"
        map diagnostic (diagnostics r) @?= [("error", 3, 11, "undefined rule T")]
    ]

-- Comparison with peg-hs gen ------------------------------------------------------

-- Run peg-hs gen in a fresh directory on a copy of the grammar, as
-- grammar/NAME and -o src/NAME.hs, or without -o; the file written, if any.
runGen :: FilePath -> Maybe FilePath -> Bool -> BS.ByteString -> IO (Maybe BS.ByteString)
runGen source output debug bytes = withSystemTempDirectory "peg-wasm-test" $ \dir -> do
  createDirectoryIfMissing True (dir </> takeDirectory source)
  mapM_ (createDirectoryIfMissing True . (dir </>) . takeDirectory) output
  BS.writeFile (dir </> source) bytes
  let args = ["gen", source] ++ maybe [] (\o -> ["-o", o]) output ++ ["--debug-entry" | debug]
      written = fromMaybe (defaultOutput source) output
  (code, _, _) <- readCreateProcessWithExitCode (proc "peg-hs" args) {cwd = Just dir} ""
  case code of
    ExitSuccess -> Just <$> BS.readFile (dir </> written)
    ExitFailure _ -> do
      exists <- doesFileExist (dir </> written)
      if exists then assertFailure "peg-hs gen failed but wrote the module" >> pure Nothing else pure Nothing
  where
    defaultOutput s = takeDirectory s </> (takeBaseName s <> ".hs")

moduleBytes :: Value -> Maybe BS.ByteString
moduleBytes r = TE.encodeUtf8 <$> asText (field "module" r)

genTest :: FilePath -> Bool -> TestTree
genTest file debug = testCase (file <> (if debug then " --debug-entry" else "")) $ do
  bytes <- BS.readFile file
  let name = takeBaseName file <> takeExtension file
      source = "grammar" </> name
      output = "src" </> (takeBaseName file <> ".hs")
  expected <- runGen source (Just output) debug bytes
  let r = analyze [("grammar", String (TE.decodeUtf8 bytes)), ("sourceName", String (T.pack source)), ("outputName", String (T.pack output)), ("debugEntry", Bool debug)]
  assertBool "peg-hs gen generates the module" (isJust expected || any (\d -> member "severity" d == Just (String "error")) (diagnostics r))
  moduleBytes r @?= expected

nameTests :: [TestTree]
nameTests =
  [ testCase "without sourceName and outputName, Grammar.hpeg and Grammar.hs" $ do
      let bytes = TE.encodeUtf8 calcGenerated
      expected <- runGen "Grammar.hpeg" Nothing False bytes
      assertBool "peg-hs gen generates" (isJust expected)
      moduleBytes (analyzeGrammar calcGenerated) @?= expected
  , testCase "with sourceName only, the outputName has the extension .hs" $ do
      let bytes = TE.encodeUtf8 calcGenerated
      expected <- runGen "grammar/Calc.hpeg" Nothing False bytes
      assertBool "peg-hs gen generates" (isJust expected)
      moduleBytes (analyze [("grammar", String calcGenerated), ("sourceName", String "grammar/Calc.hpeg")]) @?= expected
  ]

-- The syntax tree -----------------------------------------------------------------

children :: Value -> [Value]
children = fromMaybe [] . asArray . field "children"

nodeCount :: Value -> Int
nodeCount v = 1 + sum (map nodeCount (children v))

-- A rendering of the tree with a node on each line, which is still JSON.
prettyTree :: Value -> Text
prettyTree = go 0
  where
    go n v = case v of
      Object ms ->
        let own = renderJson (Object (filter ((/= "children") . fst) ms))
            cs = children v
            open = T.dropEnd 1 own <> ",\"children\":["
         in if null cs
              then open <> "]}"
              else open <> "\n" <> T.intercalate ",\n" [T.replicate (n + 1) "  " <> go (n + 1) c | c <- cs] <> "]}"
      _ -> renderJson v

-- One of each kind of node that the notation writes.
astGrammar :: Text
astGrammar =
  T.unlines
    [ "%module Ast.Sample"
    , "%start Doc"
    , "%entry Pair"
    , "%export Doc, Item(..)"
    , "%env Int"
    , "%tabstop 4"
    , "%nomemo Sp"
    , "%language OverloadedStrings, LambdaCase"
    , "%recover l Skip"
    , "%safe l"
    , "%expect Pair \"a \\\"pair\\\"\" # comment"
    , "%message l \"an l # not a comment\""
    , "%deriving Eq, Show"
    , "%{"
    , "import Data.Text (Text)"
    , "}%"
    , ""
    , "Doc :: [Text]"
    , "Doc <- xs:Lines<Item(0)> Pair !. { xs }"
    , ""
    , "Lines<p :: a> :: [a]"
    , "Lines<p> <- x:p xs:('\\n' p)* { x : xs }"
    , ""
    , "Item(n :: Int) :: Text"
    , "Item <- &{ n >= 0 } !{ n > 9 } s:$([a-z] / \"_\")+ &(.) ('.' ^l)? { s }"
    , ""
    , "Pair <- Item(1) Sp Item(2) @Two"
    , "     / Item(1) @One"
    , ""
    , "Skip <- (!'\\n' .)*"
    , ""
    , "Sp <- ' '*"
    ]

-- The nodes of a grammar, counted from the grammar: one for each value of
-- the table of ADR 0078. Each directive is on a line of its own.
grammarNodes :: Grammar -> Int
grammarNodes g = 1 + directives + values + length (grammarVerbatim g) + sum (map rule (grammarRules g))
  where
    lines' =
      map locLine $
        [locOf (grammarModule g)]
          ++ map locOf (maybe [] pure (grammarStart g) ++ grammarEntries g ++ grammarExports g ++ maybe [] pure (grammarEnv g) ++ grammarNoMemo g ++ grammarLanguages g ++ grammarTokens g ++ grammarTrivia g ++ grammarInline g ++ grammarSafe g)
          ++ maybe [] (pure . locOf) (grammarTabstop g)
          ++ maybe [] pure (grammarSyntax g)
          ++ map (locOf . fst) (grammarRecovers g ++ grammarExpects g ++ grammarMessages g)
          ++ maybe [] (pure . locOf) (grammarDeriving g)
    directives = length (dedup (sort lines'))
    dedup (a : b : xs) | a == b = dedup (b : xs)
    dedup (a : xs) = a : dedup xs
    dedup [] = []
    values =
      1
        + length (maybe [] pure (grammarStart g) ++ grammarEntries g ++ grammarExports g ++ maybe [] pure (grammarEnv g) ++ grammarNoMemo g ++ grammarLanguages g ++ grammarTokens g ++ grammarTrivia g ++ grammarInline g ++ grammarSafe g)
        + maybe 0 (const 1) (grammarTabstop g)
        + 2 * length (grammarRecovers g ++ grammarExpects g ++ grammarMessages g)
        + maybe 0 (length . unLoc) (grammarDeriving g)
    rule r = 1 + length (ruleParams r) + length (ruleTemplateParams r) + maybe 0 (const 1) (ruleAnnotation r) + sum (map alt (ruleAlts r))
    alt a = 1 + sum (map item (altItems a)) + maybe 0 (const 1) (altAction a) + maybe 0 (const 1) (altConstructor a)
    item i = 1 + expr (itemExpr i)
    expr = \case
      ELit {} -> 1
      EClass {} -> 1
      EAny -> 1
      ERef _ _ args -> 1 + length args
      EGroup seqs -> 1 + sum [1 + sum (map item s) | s <- seqs]
      EStar e -> 1 + expr e
      EPlus e -> 1 + expr e
      EOpt e -> 1 + expr e
      EAnd e -> 1 + expr e
      ENot e -> 1 + expr e
      ECapture e -> 1 + expr e
      EDiscard e -> 1 + expr e
      ELabel _ e _ -> 1 + expr e
      EPred {} -> 1
      ETemplate _ _ es args -> 1 + sum (map expr es) + length args

astTests :: [FilePath] -> TestTree
astTests conformance =
  testGroup
    "the syntax tree"
    [ goldenVsString "a grammar with every kind of node" "test/golden/ast.json" $ do
        let r = analyzeGrammar astGrammar
        diagnostics r @?= []
        pure (BL.fromStrict (TE.encodeUtf8 (prettyTree (field "ast" r) <> "\n")))
    , testCase "the golden file is the tree as JSON" $ do
        golden <- TIO.readFile "test/golden/ast.json"
        parseJson golden @?= Just (field "ast" (analyzeGrammar astGrammar))
    , testCase "%expect and %message have a name and the string as written (ADR 0089)" $ do
        let r = analyzeGrammar "%module A\n%expect S \"an \\\"s\\\"\"  # c\n%message l \"x # y\"\nS <- 'a' ^l\n"
            directives = [c | c <- children (field "ast" r), textOf "kind" c == "Directive"]
            values c = [(textOf "text" v, member "line" v >>= asInt, member "column" v >>= asInt) | v <- children c]
        diagnostics r @?= []
        map values (drop 1 directives) @?= [[("S", Just 2, Just 9), ("\"an \\\"s\\\"\"", Just 2, Just 11)], [("l", Just 3, Just 10), ("\"x # y\"", Just 3, Just 12)]]
    , testCase "the children of the grammar are in the order of their locations" $ do
        let r = analyzeGrammar "%module A\nS <- 'a' T\n%start S\nT <- 'b'\n%{\nx = 1\n}%\n%nomemo T\n"
            cs = children (field "ast" r)
        map (textOf "kind") cs @?= ["Directive", "Rule", "Directive", "Rule", "Verbatim", "Directive"]
        map (\c -> (member "line" c >>= asInt, member "column" c >>= asInt)) cs @?= [(Just 1, Just 1), (Just 2, Just 1), (Just 3, Just 1), (Just 4, Just 1), (Just 6, Just 1), (Just 8, Just 1)]
    , testGroup
        "the nodes of the conformance grammars are those of the grammar"
        [ testCase f $ do
            src <- TIO.readFile f
            case parseGrammar src of
              Left ds -> assertFailure (show ds)
              Right g -> nodeCount (field "ast" (analyzeGrammar src)) @?= grammarNodes g
        | f <- conformance
        ]
    ]

-- Formatting ----------------------------------------------------------------------

formatTests :: [FilePath] -> TestTree
formatTests conformance =
  testGroup
    "format"
    [ testGroup
        "the text is that of formatGrammar, and formatting it again changes nothing"
        [ testCase f $ do
            src <- TIO.readFile f
            let r = format src
            diagnostics r @?= []
            Right (textOf "text" r) @?= formatGrammar src
            textOf "text" (format (textOf "text" r)) @?= textOf "text" r
        | f <- conformance
        ]
    , testCase "a syntax error has no text and a located error" $ do
        let r = format "%module A\n\nS <- ('a'\n"
        field "text" r @?= Null
        case map diagnostic (diagnostics r) of
          [("error", l, c, m)] -> assertBool "a location and a message" (l > 0 && c > 0 && not (T.null m))
          ds -> assertFailure ("one error expected: " <> show ds)
    ]

-- Requests that are wrong ---------------------------------------------------------

requestTests :: TestTree
requestTests =
  testGroup
    "requests that are wrong get only an error"
    $ [ testCase (name <> " to " <> T.unpack fname) $ case response (f req) of
        Object [("error", String e)] -> assertBool "a message" (not (T.null e))
        v -> assertFailure (T.unpack (renderJson v))
    | (fname, f) <- [("analyze", analyzeJson), ("format", formatJson)]
    , (name, req) <-
        [ ("not JSON", "{\"grammar\": ")
        , ("no grammar", "{\"sourceName\": \"A.hpeg\"}")
        , ("a grammar that is not a string", "{\"grammar\": 1}")
        , ("an array", "[\"%module A\"]")
        ]
    ]
      ++ [ testCase (name <> " to analyze") $ case response (analyzeJson req) of
             Object [("error", String _)] -> pure ()
             v -> assertFailure (T.unpack (renderJson v))
         | (name, req) <-
             [ ("a sourceName that is not a string", "{\"grammar\": \"%module A\\nS <- 'a'\\n\", \"sourceName\": 1}")
             , ("an outputName that is not a string", "{\"grammar\": \"%module A\\nS <- 'a'\\n\", \"outputName\": true}")
             , ("a debugEntry that is not a boolean", "{\"grammar\": \"%module A\\nS <- 'a'\\n\", \"debugEntry\": \"yes\"}")
             ]
         ]

-- The fixes of the security audit of 2026-11-07 (ADR 0080).
auditFixTests :: TestTree
auditFixTests =
  testGroup
    "security fixes (ADR 0080)"
    [ testCase "the request of the audit with a newline in sourceName gets a diagnostic and no module (SEC-05)" $ do
        exists <- doesFileExist "../docs/audits/2026-11-07-srcname-req.json"
        if not exists
          then pure ()
          else do
            req <- TIO.readFile "../docs/audits/2026-11-07-srcname-req.json"
            let r = response (analyzeJson req)
            map diagnostic (diagnostics r) @?= [("error", 1, 1, "the file name contains a control character")]
            field "module" r @?= Null
    , testCase "an outputName with a control character gets a diagnostic and no module (SEC-05)" $ do
        let r = analyze [("grammar", String "%module A\nS <- 'a'\n"), ("outputName", String "A.hs\r")]
        map diagnostic (diagnostics r) @?= [("error", 1, 1, "the file name contains a control character")]
        field "module" r @?= Null
    , testCase "a grammar of 257 levels gets a diagnostic from analyze and format (SEC-06)" $ do
        let g = "%module A\nS <- " <> T.replicate 257 "(" <> "'a'" <> T.replicate 257 ")" <> "\n"
            expected = [("error", 2, 262, "the expression nests deeper than 256")]
        map diagnostic (diagnostics (analyzeGrammar g)) @?= expected
        map diagnostic (diagnostics (format g)) @?= expected
        field "text" (format g) @?= Null
    , testCase "a request whose grammar is an array of 257 levels gets only an error (SEC-06)" $
        forM_ [analyzeJson, formatJson] $ \f ->
          case response (f ("{\"grammar\": " <> T.replicate 257 "[" <> T.replicate 257 "]" <> "}")) of
            Object [("error", String e)] -> e @?= "the request is not JSON"
            v -> assertFailure (T.unpack (renderJson v))
    ]
