-- | Tests of the libraries in the language server (ADR 0092).
module Imports (importTests) where

import Control.Exception (bracket_)
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Lsp (runServer)
import Peg.Lsp.Json
import Peg.Lsp.Rpc
import Peg.Lsp.Server
import System.Directory
import System.FilePath ((</>))
import System.IO (IOMode (..), withBinaryFile)
import Test.Tasty
import Test.Tasty.HUnit

importTests :: TestTree
importTests =
  testGroup
    "libraries (ADR 0092)"
    [ testCase "opening a grammar asks to read its libraries, and their texts give the diagnostics" $ do
        let s1 = handleMessage started (openAt rootUri calc)
        stepReads s1 @?= [FileRequest libUri "/w" "lex/Ident.hpeg"]
        diagnosticsOf rootUri (stepOutput s1) @?= Nothing
        let s2 = withPending (receiveFiles (stepState s1) [(libUri, Right ident)])
        diagnosticsOf rootUri (stepOutput s2) @?= Just []
    , testCase "an error in a library is at the %import, with the line and column in the library" $
        diagnosticsOf rootUri (stepOutput (opened [(libUri, Right (ident <> "Bad <- Missing\n"))] (T.replace "Ident '=' Sp" "Ident Bad '=' Sp" calc)))
          @?= Just [(1, "lex/Ident.hpeg:11:8: undefined rule Missing")]
    , testCase "a library that cannot be read is an error at the %import" $
        diagnosticsOf rootUri (stepOutput (opened [(libUri, Left "no such file")] calc))
          @?= Just [(1, "cannot import lex/Ident.hpeg: no such file")]
    , testCase "go to the definition of an imported rule" $ do
        let st = stepState (opened [(libUri, Right ident)] calc)
            out = stepOutput (handleMessage st (request 2 "textDocument/definition" (positionIn rootUri 4 12)))
        resultOf out @?= Just (object [("uri", String libUri), ("range", rangeOf (3, 0) (3, 5))])
    , testCase "the hover of an imported rule shows its type" $ do
        let st = stepState (opened [(libUri, Right ident)] calc)
            out = stepOutput (handleMessage st (request 2 "textDocument/hover" (positionIn rootUri 4 12)))
        (resultOf out >>= member "contents" >>= member "value" >>= asText) @?= Just "```peg\nIdent :: Text\n```"
    , testCase "the hover of an imported rule without a type annotation shows its inferred type" $ do
        let st = stepState (opened [(libUri, Right ident)] calc)
            out = stepOutput (handleMessage st (request 2 "textDocument/hover" (positionIn rootUri 4 22)))
        (resultOf out >>= member "contents" >>= member "value" >>= asText) @?= Just "```peg\nSp :: ()\n```"
    , testCase "changing an open library checks the grammars that import it again" $ do
        let s1 = handleMessage started (openAt libUri ident)
            s2 = handleMessage (stepState s1) (openAt rootUri calc)
        stepReads s2 @?= []
        diagnosticsOf rootUri (stepOutput s2) @?= Just []
        let s3 = handleMessage (stepState s2) (changeAt libUri (T.replace "Sp <- [ \\t]*" "Sp <- [ \\t]* Missing" ident))
        diagnosticsOf rootUri (stepOutput s3) @?= Just [(1, "lex/Ident.hpeg:10:14: undefined rule Missing")]
        diagnosticsOf libUri (stepOutput s3) @?= Just [(9, "undefined rule Missing")]
    , testCase "an %import of a grammar that is not a file is an error" $
        diagnosticsOf "untitled:Untitled-1" (stepOutput (handleMessage started (openAt "untitled:Untitled-1" calc)))
          @?= Just [(1, "imports need a file: save the grammar first")]
    , testCase "the URI of a library is under the directory of the grammar" $
        stepReads (handleMessage started (openAt "file:///a%20b/c/G.hpeg" calc)) @?= [FileRequest "file:///a%20b/c/lex/Ident.hpeg" "/a b/c" "lex/Ident.hpeg"]
    , fileTest
    ]

calc :: Text
calc = T.unlines ["%module Calc.Parser", "%import lex/Ident.hpeg", "", "Assign :: (Text, Text)", "Assign <- n:Ident '=' Sp v:Ident { (n, v) }"]

ident :: Text
ident = T.unlines ["%library", "", "Ident :: Text", "Ident <- $(IdentStart IdentChar*) Sp", "", "IdentStart <- [a-zA-Z_]", "", "IdentChar <- [a-zA-Z0-9_]", "", "Sp <- [ \\t]*"]

rootUri :: Text
rootUri = "file:///w/Calc.hpeg"

libUri :: Text
libUri = "file:///w/lex/Ident.hpeg"

started :: State
started = stepState (handleMessage initialState (request 1 "initialize" (object [])))

-- The grammar opened, the files read given, and the pending diagnostics.
opened :: [(Text, Either Text Text)] -> Text -> Step
opened files src = withPending (receiveFiles (stepState (handleMessage started (openAt rootUri src))) files)

withPending :: Step -> Step
withPending s = let p = publishPending (stepState s) in p {stepOutput = stepOutput s ++ stepOutput p}

-- The diagnostics published last for a URI, as the line (from 0) and the
-- message of each.
diagnosticsOf :: Text -> [Value] -> Maybe [(Int, Text)]
diagnosticsOf u out =
  case reverse [ds | m <- out, member "method" m == Just (String "textDocument/publishDiagnostics"), Just p <- [member "params" m], member "uri" p == Just (String u), Just ds <- [member "diagnostics" p >>= asArray]] of
    ds : _ -> Just [(line, msg) | d <- ds, Just line <- [member "range" d >>= member "start" >>= member "line" >>= asInt], Just msg <- [member "message" d >>= asText]]
    [] -> Nothing

resultOf :: [Value] -> Maybe Value
resultOf out = case [r | m <- out, Just r <- [member "result" m]] of
  r : _ -> Just r
  [] -> Nothing

request :: Int -> Text -> Value -> Value
request i m p = object [("jsonrpc", String "2.0"), ("id", int i), ("method", String m), ("params", p)]

notify :: Text -> Value -> Value
notify m p = object [("jsonrpc", String "2.0"), ("method", String m), ("params", p)]

openAt :: Text -> Text -> Value
openAt u t = notify "textDocument/didOpen" (object [("textDocument", object [("uri", String u), ("languageId", String "peg"), ("version", int 1), ("text", String t)])])

changeAt :: Text -> Text -> Value
changeAt u t = notify "textDocument/didChange" (object [("textDocument", object [("uri", String u), ("version", int 2)]), ("contentChanges", Array [object [("text", String t)]])])

positionIn :: Text -> Int -> Int -> Value
positionIn u l c = object [("textDocument", object [("uri", String u)]), ("position", object [("line", int l), ("character", int c)])]

rangeOf :: (Int, Int) -> (Int, Int) -> Value
rangeOf (a, b) (c, d) = object [("start", object [("line", int a), ("character", int b)]), ("end", object [("line", int c), ("character", int d)])]

-- The server over handles reads the libraries from the disk, and does not
-- follow a symbolic link.
fileTest :: TestTree
fileTest =
  testCase "the server reads a library from the disk, and not through a symbolic link" $ do
    tmp <- getTemporaryDirectory >>= canonicalizePath
    let root = tmp </> "peg-lsp-import-test"
        grammarUri name = "file://" <> T.pack (root </> "grammar" </> name)
    bracket_ (removePathForcibly root >> createDirectoryIfMissing True (root </> "grammar" </> "lex")) (removePathForcibly root) $ do
      createDirectoryIfMissing True (root </> "outside")
      TIO.writeFile (root </> "grammar" </> "lex" </> "Ident.hpeg") ident
      TIO.writeFile (root </> "outside" </> "Ident.hpeg") ident
      createDirectoryLink (root </> "outside") (root </> "grammar" </> "linked")
      let input = root </> "in"
          output = root </> "out"
          msgs =
            [ request 1 "initialize" (object [])
            , openAt (grammarUri "Calc.hpeg") calc
            , openAt (grammarUri "Linked.hpeg") (T.replace "lex/Ident.hpeg" "linked/Ident.hpeg" calc)
            ]
      BS.writeFile input (BS.concat (map encodeMessage msgs))
      _ <- withBinaryFile input ReadMode $ \i -> withBinaryFile output WriteMode $ \o -> runServer i o
      bytes <- BS.readFile output
      let out = [v | Right body <- fst (decodeFrames bytes), Just v <- [parseJson body]]
      diagnosticsOf (grammarUri "Calc.hpeg") out @?= Just []
      diagnosticsOf (grammarUri "Linked.hpeg") out @?= Just [(1, "cannot import linked/Ident.hpeg: it is a symbolic link")]
