-- | Tests of the language server (ADR 0035).
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Data.Bits (xor)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy as BL
import Data.Char (isAlphaNum)
import Data.List (sort, sortOn)
import Data.Word (Word64)
import Numeric (showHex)
import Data.Maybe (fromMaybe, isJust, listToMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Grammar (Diagnostic (..), Loc (..))
import Peg.Grammar.Highlight
import Peg.Grammar.LabelInsertion (insertLabels)
import Peg.Lsp (runServer)
import Peg.Lsp.Json
import Peg.Lsp.Rpc
import Peg.Lsp.Server
import System.Directory (doesDirectoryExist, doesPathExist, getTemporaryDirectory, listDirectory, removeFile)
import System.FilePath (takeExtension, (</>))
import System.IO (IOMode (..), withBinaryFile)
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main = do
  grammars <- grammarFiles
  defaultMain $
    testGroup
      "peg-lsp"
      [ fasterChecksTests grammars
      , incrementalTests grammars
      , testGroup
          "framing and JSON"
          [ testProperty "framed messages read back in any chunks" $
              forAll (listOf genValue) $ \vs -> forAll (genSplits (BS.concat (map encodeMessage vs))) $ \chunks ->
                readAll chunks === map (Right . renderJson) vs
          , testProperty "JSON reads back what it writes" $
              forAll genValue $ \v -> parseJson (renderJson v) === Just v
          , testCase "a header without a length is an error, and the next message is read" $
              fst (decodeFrames ("X: 1\r\n\r\n" <> encodeMessage Null)) @?= [Left "a message header without Content-Length", Right "null"]
          ]
      , securityTests
      , goldenVsString "a session" "test/golden/session.txt" (pure (BL.fromStrict (TE.encodeUtf8 (T.unlines (map renderJson (session sessionMessages))))))
      , testCase "UTF-16 positions count surrogate pairs" $ do
          -- U+1D465 is a letter outside the basic multilingual plane.
          let src = "%module M\n\nS :: ()\nS <- a\x1D465 b { () }\n\na\x1D465 :: ()\na\x1D465 <- 'x' { () }\n\nb :: ()\nb <- 'b' { () }\n"
              results = [r | m <- session [initialize False, open src, request 2 "textDocument/definition" (docAt 3 9), request 3 "textDocument/definition" (docAt 3 5)], Just r <- [member "result" m]]
          drop 1 results @?= [object [("uri", String uri), ("range", rangeOf (9, 0) (9, 1))], object [("uri", String uri), ("range", rangeOf (6, 0) (6, 3))]]
      , skippedWithout "../peg-grammar/grammar/Peg.hpeg" "the semantic tokens are ranges of the syntax tree" $ do
          src <- TIO.readFile "../peg-grammar/grammar/Peg.hpeg"
          let out = session [initialize True, open src, request 2 "textDocument/semanticTokens/full" (object [("textDocument", object [("uri", String uri)])])]
              tokens = decodeTokens src (fromMaybe [] (lastResult out >>= member "data" >>= asArray))
              hs = fromMaybe [] (highlights src)
          assertBool "tokens" (length tokens > 100)
          [t | t@(a, b) <- tokens, (a, b) `notElem` [(hlStart h, hlEnd h) | h <- hs], (a, b) `notElem` [(hlStart h, Loc (locLine (hlEnd h)) (locColumn (hlEnd h) - 1)) | h <- hs, hlKind h == HBinding]] @?= []
      , testProperty "every request has one response, and nothing throws" $
          withNumTests 300 $
            forAll genSession $ \msgs -> ioProperty $ do
              r <- try (evaluate (let out = session msgs in sum (map (T.length . renderJson) out) `seq` out))
              pure $ case r of
                Left (e :: SomeException) -> counterexample (show e) False
                Right out ->
                  let ids xs = sort (mapMaybe (\m -> member "id" m >>= asInt) xs)
                   in ids out === ids [m | m <- msgs, member "method" m /= Nothing]
      , testCase "an info of the linter has the severity Hint (ADR 0067)" $ do
          let src = "%module M\nS :: ()\nS <- 'a' { () }\n"
          [(sev, locLine l, locColumn l, code) | (sev, Diagnostic l _, code) <- diagnose src]
            @?= [(Hint, 2, 1, Just "omittable-unit-annotation"), (Hint, 3, 10, Just "omittable-unit-action")]
          let out = T.concat (map renderJson (session [initialize False, open src]))
          assertBool (T.unpack out) ("\"severity\":4,\"source\":\"peg-hs\",\"message\":\"the action can be omitted" `T.isInfixOf` out)
      , testCase "the hover of a rule without a type annotation shows () (ADR 0066)" $ do
          let src = "%module M\n\nS :: Int\nS <- A { 1 }\n\nA <- 'a'\n"
              results = [r | m <- session [initialize False, open src, request 2 "textDocument/hover" (docAt 3 5), request 3 "textDocument/hover" (docAt 5 0)], Just r <- [member "result" m]]
              contents r = member "contents" r >>= member "value"
          map contents (drop 1 results) @?= [Just (String "```peg\nA :: ()\n```"), Just (String "```peg\nA :: ()\n```")]
      , generatedTypeTests
      , testCase "a predicate that refers to a binding on its right is an error at the name (ADR 0082)" $
          [(locLine l, locColumn l, m) | (Error, Diagnostic l m, _) <- diagnose "%module M\nS :: Int\nS <- &{ y > 0 } y:N { y }\nN :: Int\nN <- [0-9] { 1 }\n"]
            @?= [(3, 9, "the predicate refers to y, which is bound to its right")]
      , testCase "a template call in a grammar without templates is an error (ADR 0052)" $
          [(locLine l, locColumn l, m) | (Error, Diagnostic l m, _) <- diagnose "%module M\nA :: ()\nA <- B<'x'> B { () }\nB :: ()\nB <- 'b' { () }\n"]
            @?= [(3, 6, "rule B is not a template")]
      , testCase "a template call with value arguments: its name is a macro, and goes to the template (ADR 0055)" $ do
          let src = "%module M\n\nS :: ()\nS <- T<'a'>(1) { () }\n\nT<p> :: ()\nT<p> <- p { () }\n"
              out = session [initialize False, open src, request 2 "textDocument/semanticTokens/full" (object [("textDocument", object [("uri", String uri)])]), request 3 "textDocument/definition" (docAt 3 5)]
              results = [r | m <- out, Just r <- [member "result" m]]
              typed = decodeTypedTokens src (fromMaybe [] (member "data" (results !! 1) >>= asArray))
          [ty | (Loc 4 6, Loc 4 7, ty) <- typed] @?= ["macro"]
          drop 2 results @?= [object [("uri", String uri), ("range", rangeOf (6, 0) (6, 1))]]
          [(locLine l, locColumn l, m) | (Error, Diagnostic l m, _) <- diagnose src]
            @?= [(4, 6, "the template T takes no value arguments")]
      , testCase "the arguments of directives: rules are functions, labels decorators and the module a namespace (ADR 0069)" $ do
          let src = "%module M\n%entry E\n%recover l R\n\nS :: ()\nS <- E ^l\n\nE :: ()\nE <- 'e'\n\nR :: ()\nR <- 'r'\n"
              out = session [initialize False, open src, request 2 "textDocument/semanticTokens/full" (object [("textDocument", object [("uri", String uri)])])]
              typed = decodeTypedTokens src (fromMaybe [] (lastResult out >>= member "data" >>= asArray))
          [(locLine a, locColumn a, locColumn b, ty) | (a, b, ty) <- typed, locLine a <= 3]
            @?= [(1, 1, 8, "keyword"), (1, 9, 10, "namespace"), (2, 1, 7, "keyword"), (2, 8, 9, "function"), (3, 1, 9, "keyword"), (3, 10, 11, "decorator"), (3, 12, 13, "function")]
          assertBool "namespace in the legend" ("namespace" `elem` tokenTypes)
      , testGroup
          "code actions (ADR 0054)"
          [ testCase "the server offers code actions" $
              (lastResult (session [initialize True]) >>= path ["capabilities", "codeActionProvider"]) @?= Just (Bool True)
          , testCase "a label at a candidate, the same as peg-hs label --write" $ do
              let actions = codeActionsAt actionGrammar "','"
              map fst actions @?= ["Add the label ^S_comma", "Add the 3 labels that are safe"]
              [applyAction actionGrammar a | (_, a) <- actions]
                @?= [Right (T.replace "',' [a-z]" "',' ^S_comma [a-z]" actionGrammar), either (Left . show) (Right . snd) (insertLabels [] actionGrammar)]
          , testCase "no label where there is no candidate" $
              filter (T.isPrefixOf "Add the label" . fst) (codeActionsAt actionGrammar "'('") @?= []
          , testCase "%recover for a reference, a literal and a class" $ do
              let recoverAt needle = [(t, applyAction actionGrammar a) | (t, a) <- codeActionsAt actionGrammar needle, "Add %recover" `T.isPrefixOf` t]
                  ruleOf out name = [l | Right o <- [out], l <- T.lines o, (name <> " ") `T.isPrefixOf` l]
              [(t, ruleOf out "Recover_num") | (t, out) <- recoverAt "Num ^num"]
                @?= [("Add %recover num and the rule Recover_num", ["Recover_num :: Int", "Recover_num <- (!',' .)* { _ }"])]
              [(t, ruleOf out "Recover_lx") | (t, out) <- recoverAt "'x' ^lx"]
                @?= [("Add %recover lx and the rule Recover_lx", ["Recover_lx :: ()", "Recover_lx <- (![\\n] .)* { _ }"])]
              [(t, ruleOf out "Recover_cl") | (t, out) <- recoverAt "[a-z] ^cl"]
                @?= [("Add %recover cl and the rule Recover_cl", ["Recover_cl :: ()", "Recover_cl <- (!')' .)* { _ }"])]
              [out | (_, out) <- recoverAt "Num ^num", Right o <- [out], (Error, _, _) <- diagnose o] @?= []
              [take 2 (drop 1 (T.lines o)) | (_, Right o) <- recoverAt "Num ^num"] @?= [["%recover blk Skip", "%recover num Recover_num"]]
          , testCase "no %recover for a group, a label with %recover, and a covered label" $
              [t | needle <- ["('y'", "B ^blk", "'c' ^inner"], (t, _) <- codeActionsAt actionGrammar needle, "Add %recover" `T.isPrefixOf` t] @?= []
          ]
      , skippedWithout "../peg-grammar/grammar/Peg.hpeg" "the notation's grammar has no errors in the server" $ do
          src <- TIO.readFile "../peg-grammar/grammar/Peg.hpeg"
          [d | (Error, d, _) <- diagnose src] @?= []
      ]

-- ADR 0075: the semantic tokens, hovers and code actions of the rules whose
-- types are inferred or generated.
generatedTypeTests :: TestTree
generatedTypeTests =
  testGroup
    "types of rules without type annotations and actions (ADR 0075)"
    [ testCase "a constructor name is an enumMember, and a class of %deriving a type" $ do
        let out = session [initialize False, open generatedGrammar, request 2 "textDocument/semanticTokens/full" (object [("textDocument", object [("uri", String uri)])])]
            typed = decodeTypedTokens generatedGrammar (fromMaybe [] (lastResult out >>= member "data" >>= asArray))
        [(locLine a, locColumn a, locColumn b, ty) | (a, b, ty) <- typed, ty `elem` ["enumMember", "type"]]
          @?= [(2, 11, 13, "type"), (2, 15, 19, "type"), (4, 26, 29, "enumMember")]
        assertBool "enumMember and type in the legend" (all (`elem` tokenTypes) ["enumMember", "type"])
    , testCase "the hovers of an inferred, a generated and a unit rule, and of a constructor" $ do
        let results = [r | m <- session (initialize False : open generatedGrammar : [request i "textDocument/hover" (docAt l c) | (i, (l, c)) <- zip [2 ..] [(3, 0), (6, 0), (8, 0), (3, 26), (3, 17)]]), Just r <- [member "result" m]]
            contents r = member "contents" r >>= member "value" >>= asText
        map contents (drop 1 results)
          @?= [ Just "```peg\nExpr :: Expr\n```\n\n```haskell\ndata Expr = Add Expr Text | Expr2 Text\n  deriving (Eq, Show)\n```"
              , Just "```peg\nNum :: Text\n```"
              , Just "```peg\nSp :: ()\n```"
              , Just "```haskell\nAdd :: Expr -> Text -> Expr\n```"
              , Just "```peg\nSp :: ()\n```"
              ]
    , testCase "a code action writes the default constructor names" $ do
        let actions = [(t, applyAction generatedGrammar a) | (t, a) <- codeActionsAt generatedGrammar "/ Num", "Write the constructor names" `T.isPrefixOf` t]
        actions @?= [("Write the constructor names of rule Expr", Right (T.replace "     / Num\n" "     / Num @Expr2\n" generatedGrammar))]
    , testCase "no code action for a rule whose type is not generated" $
        [t | (t, _) <- codeActionsAt generatedGrammar "Num <-", "Write the constructor names" `T.isPrefixOf` t] @?= []
    ]

generatedGrammar :: Text
generatedGrammar =
  T.unlines
    [ "%module M"
    , "%deriving Eq, Show"
    , ""
    , "Expr <- Expr '+' Sp Num @Add"
    , "     / Num"
    , ""
    , "Num <- $[0-9]+ Sp"
    , ""
    , "Sp <- ' '*"
    ]

-- A grammar for the code actions: labels on a reference, a literal, a class
-- and a group, a label with %recover and a label it covers.
actionGrammar :: Text
actionGrammar =
  T.unlines
    [ "%module M"
    , "%recover blk Skip"
    , ""
    , "S :: Int"
    , "S <- '(' n:Num ^num ',' [a-z] ^cl ('y' 'z') ^grp ')' B ^blk 'x' ^lx { n }"
    , ""
    , "Num :: Int"
    , "Num <- [0-9]+ { 1 }"
    , ""
    , "B :: ()"
    , "B <- 'b' 'c' ^inner { () }"
    , ""
    , "Skip :: ()"
    , "Skip <- { () }"
    ]

-- The code actions at the first occurrence of a text, with their titles.
codeActionsAt :: Text -> Text -> [(Text, Value)]
codeActionsAt src needle =
  let (before, _) = T.breakOn needle src
      line = T.count "\n" before
      ch = T.length (snd (T.breakOnEnd "\n" before))
      params = object [("textDocument", object [("uri", String uri)]), ("range", rangeOf (line, ch) (line, ch)), ("context", object [("diagnostics", Array [])])]
      out = session [initialize True, open src, request 2 "textDocument/codeAction" params]
   in [(t, a) | Just (Array as) <- [lastResult out], a <- as, Just t <- [member "title" a >>= asText]]

-- The text after the edits of a code action, in a document of ASCII.
applyAction :: Text -> Value -> Either String Text
applyAction src a = case path ["edit", "changes", uri] a >>= asArray of
  Nothing -> Left "no edits"
  Just es -> do
    edits <- mapM edit es
    pure (foldr insert src (sortOn fst (zip (map fst edits) [0 :: Int ..]) `withTexts` edits))
  where
    ls = T.splitOn "\n" src
    edit e = maybe (Left "a bad edit") Right $ do
      l <- path ["range", "start", "line"] e >>= asInt
      c <- path ["range", "start", "character"] e >>= asInt
      t <- member "newText" e >>= asText
      pure (sum (map ((+ 1) . T.length) (take l ls)) + c, t)
    withTexts order es = [(o, snd (es !! k)) | (o, k) <- order]
    insert (o, t) acc = T.take o acc <> t <> T.drop o acc

-- Run messages through the server from its initial state, until it exits.
session :: [Value] -> [Value]
session = go initialState
  where
    go _ [] = []
    go st (m : ms) =
      let step = handleMessage st m
       in stepOutput step ++ maybe (go (stepState step) ms) (const []) (stepExit step)

readAll :: [BS.ByteString] -> [Either Text Text]
readAll = go BS.empty
  where
    go buf [] = fst (decodeFrames buf)
    go buf (c : cs) = let (ms, rest) = decodeFrames (buf <> c) in ms ++ go (either (error . show) id rest) cs

genSplits :: BS.ByteString -> Gen [BS.ByteString]
genSplits b
  | BS.null b = pure []
  | otherwise = do
      n <- choose (1, max 1 (BS.length b))
      (BS.take n b :) <$> genSplits (BS.drop n b)

genValue :: Gen Value
genValue = sized go
  where
    go n
      | n <= 1 = leaf
      | otherwise =
          frequency
            [ (3, leaf)
            , (1, Array <$> resize (n `div` 2) (listOf (go (n `div` 3))))
            , (1, Object <$> resize (n `div` 2) (listOf ((,) <$> text <*> go (n `div` 3))))
            ]
    leaf = oneof [pure Null, Bool <$> arbitrary, int <$> arbitrary, pure (Number "-1.5e3"), String <$> text]
    text = T.pack <$> listOf (elements "ab \"\\\n\t\1\x7f\233\128512")

-- Messages -----------------------------------------------------------------------

uri :: Text
uri = "file:///grammar.hpeg"

request :: Int -> Text -> Value -> Value
request i m p = object [("jsonrpc", String "2.0"), ("id", int i), ("method", String m), ("params", p)]

notify :: Text -> Value -> Value
notify m p = object [("jsonrpc", String "2.0"), ("method", String m), ("params", p)]

initialize :: Bool -> Value
initialize utf8 =
  request 1 "initialize" (object [("capabilities", object [("general", object [("positionEncodings", Array [String "utf-8" | utf8] )])])])

open :: Text -> Value
open t = notify "textDocument/didOpen" (object [("textDocument", object [("uri", String uri), ("languageId", String "peg"), ("version", int 1), ("text", String t)])])

change :: Text -> Value
change t = notify "textDocument/didChange" (object [("textDocument", object [("uri", String uri), ("version", int 2)]), ("contentChanges", Array [object [("text", String t)]])])

docAt :: Int -> Int -> Value
docAt l c = object [("textDocument", object [("uri", String uri)]), ("position", object [("line", int l), ("character", int c)])]

rangeOf :: (Int, Int) -> (Int, Int) -> Value
rangeOf (a, b) (c, d) = object [("start", object [("line", int a), ("character", int b)]), ("end", object [("line", int c), ("character", int d)])]

lastResult :: [Value] -> Maybe Value
lastResult out = case reverse [r | m <- out, Just r <- [member "result" m]] of
  r : _ -> Just r
  [] -> Nothing

good :: Text
good =
  T.unlines
    [ "%module M"
    , ""
    , "Expr :: Int"
    , "Expr <- l:Expr '+' r:Term { l + r }"
    , "     / x:Term"
    , ""
    , "List<p :: a> :: [a]"
    , "List<p> <- x:p xs:(',' p)* { x : xs }"
    , ""
    , "Term :: Int"
    , "Term <- d:$[0-9]+ ^digits { read (show d) }"
    , "     / '(' Expr ')' { 0 }"
    ]

broken :: Text
broken = T.replace "'(' Expr ')'" "'(' Expr ')" good

unformatted :: Text
unformatted = T.replace "l:Expr '+'" "l:Expr    '+'" good <> "Unused :: ()\nUnused <- 'a'? { () } / 'b' { () }\n"

sessionMessages :: [Value]
sessionMessages =
  [ request 0 "textDocument/hover" (docAt 0 0)
  , initialize True
  , notify "initialized" (object [])
  , open good
  , request 2 "textDocument/definition" (docAt 3 10)
  , request 3 "textDocument/references" (object [("textDocument", object [("uri", String uri)]), ("position", object [("line", int 3), ("character", int 25)]), ("context", object [("includeDeclaration", Bool True)])])
  , request 4 "textDocument/hover" (docAt 3 25)
  , request 5 "textDocument/documentSymbol" (object [("textDocument", object [("uri", String uri)])])
  , request 6 "textDocument/semanticTokens/full" (object [("textDocument", object [("uri", String uri)])])
  , request 7 "textDocument/formatting" (object [("textDocument", object [("uri", String uri)]), ("options", object [])])
  , change unformatted
  , request 8 "textDocument/formatting" (object [("textDocument", object [("uri", String uri)]), ("options", object [])])
  , change broken
  , request 9 "textDocument/documentSymbol" (object [("textDocument", object [("uri", String uri)])])
  , request 10 "textDocument/definition" (docAt 3 10)
  , request 11 "textDocument/formatting" (object [("textDocument", object [("uri", String uri)]), ("options", object [])])
  , request 15 "textDocument/hover" (docAt 3 25)
  , request 16 "textDocument/references" (object [("textDocument", object [("uri", String uri)]), ("position", object [("line", int 3), ("character", int 25)]), ("context", object [("includeDeclaration", Bool False)])])
  , request 17 "textDocument/semanticTokens/full" (object [("textDocument", object [("uri", String uri)])])
  , request 12 "textDocument/unknown" (object [])
  , notify "textDocument/didClose" (object [("textDocument", object [("uri", String uri)])])
  , request 13 "shutdown" Null
  , request 14 "textDocument/hover" (docAt 0 0)
  , notify "exit" Null
  ]

-- Random sessions: documents made of pieces of grammars, and requests at
-- random positions.
genSession :: Gen [Value]
genSession = do
  docs <- listOf1 genDoc
  reqs <- listOf (genRequest)
  let ms = zipWith (\i r -> r i) [2 ..] reqs
  pure ([initialize True, open good] ++ concat [[change d] ++ take 2 ms | d <- docs] ++ ms ++ [request 1000 "shutdown" Null, notify "exit" Null])
  where
    genDoc = T.concat <$> listOf (elements ["%module M\n", "A :: ()\n", "A <- 'a' { () }\n", "B<p> <- p", " / ", "(", ")", "{", "}", "'", "x:", "^l", "\n", "[a-z]", "#c\n", "&{ x }", "A<'b'>", "\128512", "%{\n", "}%\n"])
    genRequest = do
      m <- elements ["textDocument/definition", "textDocument/references", "textDocument/hover", "textDocument/documentSymbol", "textDocument/semanticTokens/full", "textDocument/formatting"]
      l <- choose (-1, 5)
      c <- choose (-1, 12)
      pure (\i -> request i m (docAt l c))

-- The ranges of semantic tokens, as locations in code points.
decodeTokens :: Text -> [Value] -> [(Loc, Loc)]
decodeTokens src vs = go 0 0 (mapMaybe asInt vs)
  where
    ls = T.splitOn "\n" src
    go line ch (dl : ds : len : _ : _ : rest) =
      let line' = line + dl
          ch' = if dl == 0 then ch + ds else ds
          text = ls !! line'
          col n = T.length (TE.decodeUtf8 (BS.take n (TE.encodeUtf8 text))) + 1
       in (Loc (line' + 1) (col ch'), Loc (line' + 1) (col (ch' + len))) : go line' ch' rest
    go _ _ _ = []

-- The ranges and the types of semantic tokens.
decodeTypedTokens :: Text -> [Value] -> [(Loc, Loc, Text)]
decodeTypedTokens src vs = zipWith (\(a, b) ty -> (a, b, ty)) (decodeTokens src vs) (types (mapMaybe asInt vs))
  where
    types (_ : _ : _ : ty : _ : rest) = (tokenTypes !! ty) : types rest
    types _ = []

-- | A test of files outside this package, which a source archive does not
-- have: without them it passes and reports that it was skipped, so that
-- the run says how many were (ADR 0046).
skippedWithout :: FilePath -> TestName -> Assertion -> TestTree
skippedWithout file name act = testCaseInfo name $ do
  exists <- doesPathExist file
  if exists then "" <$ act else pure ("skipped: " <> file <> " is not in a source archive")

-- Tests of ADR 0070 ------------------------------------------------------------

fasterChecksTests :: [FilePath] -> TestTree
fasterChecksTests grammars =
  testGroup
    "faster checks (ADR 0070)"
    [ skippedWithout memoGrammar "10 didChange in a row get the diagnostics of the last version only" $ do
        src <- TIO.readFile memoGrammar
        let versions = [src <> "\nExtra" <> T.pack (show k) <> " <- 'x'\n" | k <- [1 .. 10 :: Int]]
            msgs = [initialize False, notify "initialized" (object []), open src] ++ map change versions
        out <- serveFile "coalesce" msgs
        let published = filter isPublish out
        length published @?= 1
        published @?= take 1 (reverse (filter isPublish (session msgs)))
        -- The last version has an error for its unreachable rule.
        assertBool "the diagnostics of the last version" ("Extra10" `T.isInfixOf` T.concat (map renderJson published))
    , testCase "requests after changes answer for the latest version" $ do
        let renamed = T.replace "Term" "Factor" good
            msgs =
              [ initialize False
              , open good
              , change unformatted
              , change renamed
              , request 2 "textDocument/hover" (docAt 3 25)
              , request 3 "textDocument/semanticTokens/full" (object [("textDocument", object [("uri", String uri)])])
              , request 4 "textDocument/documentSymbol" (object [("textDocument", object [("uri", String uri)])])
              ]
            responses = filter (\m -> (member "id" m >>= asInt) `notElem` [Nothing, Just 1])
        out <- serveFile "requests" msgs
        responses out @?= responses (session msgs)
        map (\m -> member "id" m >>= asInt) (responses out) @?= map Just [2, 3, 4]
        (lastResultOf 2 out >>= path ["contents", "value"]) @?= Just (String "```peg\nFactor :: Int\n```")
    , testGroup
        "the diagnostics of every grammar of the repository and its mutants are unchanged"
        [ goldenVsString f ("test/golden/diagnostics" </> goldenName f) (BL.fromStrict . TE.encodeUtf8 <$> diagnosticsRecord f)
        | f <- grammars
        ]
    ]
  where
    memoGrammar = "../../conformance/bench/Memo.hpeg"
    isPublish m = member "method" m == Just (String "textDocument/publishDiagnostics")
    lastResultOf i out = listToMaybe [r | m <- out, (member "id" m >>= asInt) == Just i, Just r <- [member "result" m]]

-- Tests of ADR 0071 ------------------------------------------------------------

incrementalTests :: [FilePath] -> TestTree
incrementalTests grammars =
  testGroup
    "incremental parsing and sync (ADR 0071)"
    [ testCase "the server asks for incremental changes" $
        (lastResult (session [initialize False]) >>= path ["capabilities", "textDocumentSync", "change"]) @?= Just (int 2)
    , testCase "a range in UTF-16 code units" $
        textAfter False "a\x1D465\&b\nc" [[edit (0, 3) (0, 3) "X"]] @?= Just "a\x1D465Xb\nc"
    , testCase "a range in bytes, with utf-8" $
        textAfter True "a\x1D465\&b\nc" [[edit (0, 5) (0, 5) "X"]] @?= Just "a\x1D465Xb\nc"
    , testCase "several changes in one notification apply in order" $
        textAfter False "ab\ncd\n" [[edit (0, 0) (0, 0) "X\n", edit (1, 0) (1, 1) "", edit (2, 1) (2, 2) "Y"]] @?= Just "X\nb\ncY\n"
    , testCase "a change of the full text among changes of ranges" $
        textAfter False "ab" [[edit (0, 0) (0, 1) "x", object [("text", String "new\n")], edit (1, 0) (1, 0) "z"]] @?= Just "new\nz"
    , testCase "a range beyond the end of a line or of the document" $ do
        textAfter False "ab\ncd" [[edit (0, 100) (1, 0) ""]] @?= Just "abcd"
        textAfter False "ab\ncd" [[edit (7, 3) (9, 0) "!"]] @?= Just "ab\ncd!"
        textAfter False "ab\r\ncd" [[edit (0, 10) (0, 10) "!"]] @?= Just "ab!\r\ncd"
    , testCase "changes in several notifications" $
        textAfter False "ab\n" [[edit (0, 1) (0, 1) "1"], [edit (0, 0) (1, 0) ""], [edit (0, 0) (0, 0) "%module M\n"]] @?= Just "%module M\n"
    , skippedWithout memoGrammar "a change of one character inside a rule parses one or two fragments" $ do
        src <- TIO.readFile memoGrammar
        let ls = T.splitOn "\n" src
            line = length (takeWhile (not . T.isInfixOf " <- ") ls) + 40
            n = length (takeWhile (not . T.isInfixOf " <- ") (drop line ls)) + line
            st = sessionState [initialize False, open src, notify "textDocument/didChange" (object [("textDocument", object [("uri", String uri), ("version", int 2)]), ("contentChanges", Array [edit (n, 0) (n, 0) "X"])])]
        assertBool "a rule" (n < length ls)
        let k = reparsedFragments st uri
        assertBool ("reparsed: " <> show k) (k `elem` [Just 1, Just 2])
    , testGroup
        "the diagnostics of a change from the grammar to each of its mutants are those of the mutant alone"
        [ testCase f $ do
            src <- TIO.readFile f
            let diagnosticsOf msgs = [m | m <- session msgs, member "method" m == Just (String "textDocument/publishDiagnostics")]
                bad = [m | m <- mutants src, drop 1 (diagnosticsOf [initialize False, open src, change m]) /= diagnosticsOf [initialize False, open m]]
            assertBool (show (length bad) <> " mutants differ, the first:\n" <> concatMap T.unpack (take 1 bad)) (null bad)
        | f <- grammars
        ]
    ]
  where
    memoGrammar = "../../conformance/bench/Memo.hpeg"
    edit (a, b) (c, d) t = object [("range", rangeOf (a, b) (c, d)), ("text", String t)]
    textAfter utf8 t changes =
      documentText (sessionState ([initialize utf8, open t] ++ [notify "textDocument/didChange" (object [("textDocument", object [("uri", String uri), ("version", int v)]), ("contentChanges", Array cs)]) | (v, cs) <- zip [2 ..] changes])) uri

-- The state of the server after messages.
sessionState :: [Value] -> State
sessionState = foldl (\st m -> stepState (handleMessage st m)) initialState

-- Run the server over a file of messages, as peg-hs lsp does over standard
-- input, and read back what it wrote. The input ends without exit, so the
-- server stops at the end of its input.
serveFile :: String -> [Value] -> IO [Value]
serveFile name msgs = do
  tmp <- getTemporaryDirectory
  let input = tmp </> ("peg-lsp-test-" <> name <> ".in")
      output = tmp </> ("peg-lsp-test-" <> name <> ".out")
  BS.writeFile input (BS.concat (map encodeMessage msgs))
  _ <- withBinaryFile input ReadMode $ \i -> withBinaryFile output WriteMode $ \o -> runServer i o
  bytes <- BS.readFile output
  removeFile input
  removeFile output
  pure [v | Right body <- fst (decodeFrames bytes), Just v <- [parseJson body]]

-- The diagnostics that the server publishes for a grammar and for each of
-- its mutants: those of the grammar in full, and a digest of those of each
-- mutant.
diagnosticsRecord :: FilePath -> IO Text
diagnosticsRecord f = do
  src <- TIO.readFile f
  let diagnosticsOf t = T.concat [renderJson m | m <- session [initialize False, open t], member "method" m == Just (String "textDocument/publishDiagnostics")]
  pure . T.unlines $
    diagnosticsOf src
      : [T.pack (show i) <> " " <> T.pack (showHex (fnv1a (TE.encodeUtf8 (diagnosticsOf m))) "") | (i, m) <- zip [0 :: Int ..] (mutants src)]

-- One character deleted or duplicated, at about 50 positions of a file: the
-- mutants of the test of the syntax tree with recovery (ADR 0035).
mutants :: Text -> [Text]
mutants src =
  concat
    [ [T.take i src <> T.drop (i + 1) src, T.take (i + 1) src <> T.drop i src]
    | i <- [0, step .. T.length src - 1]
    ]
  where
    step = max 1 (T.length src `div` 50)

-- The 64-bit FNV-1a hash.
fnv1a :: BS.ByteString -> Word64
fnv1a = BS.foldl' (\h b -> (h `xor` fromIntegral b) * 1099511628211) 14695981039346656037

goldenName :: FilePath -> FilePath
goldenName f = map (\c -> if isAlphaNum c then c else '-') (dropWhile (\c -> c == '.' || c == '/') f) <> ".txt"

-- Every grammar of the repository. Directories outside this package are
-- missing in a source archive, and are skipped.
grammarFiles :: IO [FilePath]
grammarFiles = concat <$> mapM pegsIn dirs
  where
    dirs =
      [ "grammar"
      , "../peg-grammar/grammar"
      , "../peg-codegen/test/fixtures"
      , "../../conformance/json"
      , "../../conformance/bench"
      , "../../conformance/commonmark"
      , "../../conformance/commonmark/v1"
      , "../../conformance/lua"
      , "../../conformance/toml"
      ]
    pegsIn d = do
      exists <- doesDirectoryExist d
      if exists
        then map (d </>) . sort . filter ((== ".hpeg") . takeExtension) <$> listDirectory d
        else pure []

-- The fixes of the security audit of 2026-11-06 (ADR 0077).
securityTests :: TestTree
securityTests =
  testGroup
    "security fixes (ADR 0077)"
    [ testCase "the server declares no capability that makes the client match glob patterns (SEC-02)" $ do
        let caps = lastResult (session [initialize False]) >>= path ["capabilities"]
        assertBool "capabilities" (isJust caps)
        [k | k <- [["workspace", "fileOperations"], ["diagnosticProvider"], ["notebookDocumentSync"]], isJust (caps >>= path k)] @?= []
    , testGroup
        "the limits of a message (SEC-04)"
        [ testCase "the limits are 64 KiB and 64 MiB" $
            (maxHeaderLength, maxContentLength) @?= (65536, 67108864)
        , testCase "a header of the limit, with its empty line, is read" $
            decodeFrames (paddedHeader maxHeaderLength 2 <> "{}") @?= ([Right "{}"], Right "")
        , testCase "a header one byte over the limit is an error" $
            decodeFrames (paddedHeader (maxHeaderLength + 1) 2 <> "{}") @?= ([], Left HeaderTooLong)
        , testCase "an unfinished header of the limit waits for the rest" $
            let b = BS.take maxHeaderLength (paddedHeader (maxHeaderLength + 10) 2)
             in decodeFrames b @?= ([], Right b)
        , testCase "an unfinished header over the limit is an error" $
            decodeFrames (BS.take (maxHeaderLength + 1) (paddedHeader (maxHeaderLength + 10) 2)) @?= ([], Left HeaderTooLong)
        , testCase "a body of the limit is read, and waited for until it is complete" $ do
            let header = "Content-Length: " <> BC.pack (show maxContentLength) <> "\r\n\r\n"
                body = BS.replicate maxContentLength 0x61
                (ms, rest) = decodeFrames (header <> body)
            (map (fmap T.length) ms, rest) @?= ([Right maxContentLength], Right "")
            let half = header <> BS.take (maxContentLength `div` 2) body
            decodeFrames half @?= ([], Right half)
        , testCase "a Content-Length over the limit is an error, before the body arrives" $
            decodeFrames ("Content-Length: " <> BC.pack (show (maxContentLength + 1)) <> "\r\n\r\n") @?= ([], Left (BodyTooLong (fromIntegral maxContentLength + 1)))
        , testCase "a Content-Length too large for an Int is an error" $
            decodeFrames "Content-Length: 99999999999999999999999\r\n\r\n" @?= ([], Left (BodyTooLong 99999999999999999999999))
        , testCase "the messages before an error are read" $
            decodeFrames (encodeMessage Null <> "Content-Length: 67108865\r\n\r\n") @?= ([Right "null"], Left (BodyTooLong 67108865))
        , testCase "the reasons name the limits" $
            map renderFrameError [HeaderTooLong, BodyTooLong 67108865]
              @?= [ "a message header longer than 65536 bytes"
                  , "a message body of 67108865 bytes, longer than 67108864 bytes"
                  ]
        ]
    ]

-- A header of a body of a length, padded to a number of bytes with its
-- empty line.
paddedHeader :: Int -> Int -> BS.ByteString
paddedHeader size len =
  let start = "Content-Length: " <> BC.pack (show len) <> "\r\nX-Padding: "
   in start <> BS.replicate (size - BS.length start - 4) 0x78 <> "\r\n\r\n"
