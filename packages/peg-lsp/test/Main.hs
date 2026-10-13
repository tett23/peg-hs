-- | Tests of the language server (ADR 0035).
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.List (sort)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Grammar (Diagnostic (..), Loc (..))
import Peg.Grammar.Highlight
import Peg.Lsp.Json
import Peg.Lsp.Rpc
import Peg.Lsp.Server
import System.Directory (doesPathExist)
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main =
  defaultMain $
    testGroup
      "peg-lsp"
      [ testGroup
          "framing and JSON"
          [ testProperty "framed messages read back in any chunks" $
              forAll (listOf genValue) $ \vs -> forAll (genSplits (BS.concat (map encodeMessage vs))) $ \chunks ->
                readAll chunks === map (Right . renderJson) vs
          , testProperty "JSON reads back what it writes" $
              forAll genValue $ \v -> parseJson (renderJson v) === Just v
          , testCase "a header without a length is an error, and the next message is read" $
              fst (decodeFrames ("X: 1\r\n\r\n" <> encodeMessage Null)) @?= [Left "a message header without Content-Length", Right "null"]
          ]
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
      , testCase "a template call in a grammar without templates is an error (ADR 0052)" $
          [(locLine l, locColumn l, m) | (Error, Diagnostic l m, _) <- diagnose "%module M\nA :: ()\nA <- B<'x'> B { () }\nB :: ()\nB <- 'b' { () }\n"]
            @?= [(3, 6, "rule B is not a template")]
      , skippedWithout "../peg-grammar/grammar/Peg.hpeg" "the notation's grammar has no errors in the server" $ do
          src <- TIO.readFile "../peg-grammar/grammar/Peg.hpeg"
          [d | (Error, d, _) <- diagnose src] @?= []
      ]

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
    go buf (c : cs) = let (ms, rest) = decodeFrames (buf <> c) in ms ++ go rest cs

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

-- | A test of files outside this package, which a source archive does not
-- have: without them it passes and reports that it was skipped, so that
-- the run says how many were (ADR 0046).
skippedWithout :: FilePath -> TestName -> Assertion -> TestTree
skippedWithout file name act = testCaseInfo name $ do
  exists <- doesPathExist file
  if exists then "" <$ act else pure ("skipped: " <> file <> " is not in a source archive")
