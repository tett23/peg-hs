-- | Benchmarks of ADR 0007. Compare results before and after a change on
-- the same machine; absolute numbers are not recorded.
module Main (main) where

import qualified Conformance.Bench.JsonCounted as JsonCounted
import qualified Conformance.Bench.JsonNomemo as JsonNomemo
import qualified Conformance.Bench.JsonSyntax as JsonSyntax
import qualified Conformance.Bench.JsonUntyped as JsonUntyped
import qualified Conformance.Bench.NestedLR8 as NestedLR8
import qualified Conformance.CommonMark as CommonMark
import qualified Conformance.Lua.Parser as Lua
import qualified Data.ByteString as B
import qualified Data.Text.Encoding as TE
import System.Directory (listDirectory)
import System.FilePath (takeExtension, (</>))
import Peg.Runtime.Syntax (syntaxRange)
import qualified Conformance.Bench.Pathological as Pathological
import Conformance.Json.Encode (encode)
import Conformance.Json.Parser (Value (..))
import qualified Conformance.Json.Parser as Json
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Ord (Down (..))
import Criterion.Main
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import GHC.Stats (RTSStats (..), getRTSStats)
import Peg.Codegen (defaultOptions, generateFromSource)
import Peg.Grammar.Check (check)
import Peg.Grammar.LabelInsertion (insertLabels, recoverProposals)
import Peg.Grammar.Labels (labelWarnings)
import Peg.Grammar.Lint (lintGrammar)
import Peg.Grammar.Incremental (Parsed (..), noFragments, parseFragments)
import Peg.Grammar.Outline (outline)
import Peg.Grammar.Parser (parseGrammar, parseTops)
import Peg.Grammar.Templates (expandTemplates)
import qualified Peg.Lsp.Json as J
import Peg.Lsp.Rpc (encodeMessage)
import Peg.Lsp.Server (diagnose, handleFrame, handleMessage, initialState, stepOutput, stepState)
import System.Environment (lookupEnv)
import Peg.Runtime.Internal (Config (..), Stats (..))
import qualified Peg.Runtime.Internal as Rt
import System.Environment (getArgs, withArgs)
import System.Mem (performMajorGC)

-- A deterministic JSON document of roughly the given number of records.
syntheticJson :: Int -> Text
syntheticJson n = encode (Array [record i | i <- [1 .. n]])
  where
    record i =
      Object
        [ (T.pack "id", Number (T.pack (show i)))
        , (T.pack "name", String (T.pack ("item " <> show i <> " \x3042\x3044\x3046")))
        , (T.pack "tags", Array [String (T.pack "a"), String (T.pack "b"), Null, Bool (even i)])
        , (T.pack "score", Number (T.pack (show i <> ".5e-3")))
        ]

-- Force the whole tree.
size :: Value -> Int
size v = case v of
  Null -> 1
  Bool b -> if b then 1 else 1
  Number t -> T.length t
  String t -> T.length t
  Array vs -> 1 + sum (map size vs)
  Object ms -> 1 + sum [T.length k + size x | (k, x) <- ms]

-- The CommonMark spec itself, rendered as one document.
specPath :: FilePath
specPath = "data/commonmark-spec-0.31.2/spec.txt"

-- The files of the Lua test suite, read as ADR 0022 reads them.
luaSources :: IO [Text]
luaSources = do
  let dir = "data/lua-5.5.1-tests"
  files <- filter ((== ".lua") . takeExtension) <$> listDirectory dir
  mapM (fmap (prepare . TE.decodeLatin1) . B.readFile . (dir </>)) files
  where
    prepare t
      | T.isPrefixOf (T.pack "#") t = T.dropWhile (/= '\n') t
      | otherwise = t

parseLua :: [Text] -> Int
parseLua = sum . map (either (const 0) (length . show) . Lua.parse)

-- An atom inside d parentheses, for the grammar of eight nested
-- left-recursive levels (ADR 0024).
nested :: Int -> Text
nested d = T.replicate d (T.pack "(") <> T.pack "x" <> T.replicate d (T.pack ")")

pathological :: Int -> Text
pathological n = T.replicate n (T.pack "a") <> T.replicate n (T.pack "b")

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--memo-report"] -> memoReport
    ["--memory", variant, n] -> memory variant (read n)
    ["--lsp-session", file, out] -> lspSession file out
    ["--lsp-messages", file, dir] -> lspMessages file dir
    ["--lsp-session", file, out, place, sync] -> lspSessionAt place sync file out
    ["--lsp-messages", file, dir, place, sync] -> lspMessagesAt place sync file dir
    _ -> benchmarks

benchmarks :: IO ()
benchmarks = do
  jsonGrammar <- TIO.readFile "json/Json.hpeg"
  json <- evaluate (force (syntheticJson 10000))
  spec <- TIO.readFile specPath >>= evaluate . force
  lua <- luaSources >>= evaluate . force
  lspGrammar <- lspGrammarPath >>= TIO.readFile >>= evaluate . force
  lsp <- lspStages lspGrammar
  defaultMain
    [ bgroup
        "json"
        [ bench ("parse " <> show (T.length json) <> " characters") (whnf (either (const 0) size . Json.parse) json)
        , bench ("parse " <> show (T.length json) <> " characters with %nomemo") (whnf (either (const 0) (size . convertNomemo) . JsonNomemo.parse) json)
        , bench ("parse " <> show (T.length json) <> " characters with %syntax, typed entry") (whnf (either (const 0) (size . convertSyntax) . JsonSyntax.parse) json)
        , bench ("parse " <> show (T.length json) <> " characters with %syntax, tree entry") (whnf (either (const 0) (snd . syntaxRange) . JsonSyntax.parseSyntax) json)
        , bench ("parse " <> show (T.length json) <> " characters with %syntax, untyped, tree entry") (whnf (either (const 0) (snd . syntaxRange) . JsonUntyped.parseSyntax) json)
        ]
    , bgroup
        "commonmark"
        [ bench ("render the spec, " <> show (T.length spec) <> " characters") (whnf (either T.length T.length . CommonMark.toHtml) spec)
        ]
    , bgroup
        "lua"
        [ bench ("parse the test suite, " <> show (sum (map T.length lua)) <> " characters") (whnf parseLua lua)
        ]
    , bgroup
        "left recursion (eight nested levels)"
        [ bench ("depth " <> show d) (whnf (fst . NestedLR8.peg'parseWith Rt.defaultConfig) (nested d))
        | d <- [10, 100, 1000]
        ]
    , bgroup
        "left recursion (pathological)"
        [ bench ("n = " <> show n) (whnf (fst . Pathological.peg'parseWith Rt.defaultConfig) (pathological n))
        | n <- [100, 200, 400]
        ]
    , bgroup
        "generator"
        [ bench "parse Json.hpeg" (whnf (either (const 0) (length . show) . parseGrammar) jsonGrammar)
        , bench "generate Json.hpeg" (whnf (either (const 0) T.length . generateFromSource defaultOptions) jsonGrammar)
        ]
    , lsp
    ]

-- The grammar of the benchmarks of the language server (ADR 0070): a
-- grammar of the repository shaped like Golem's, or the file that
-- PEG_BENCH_LSP_GRAMMAR names.
lspGrammarPath :: IO FilePath
lspGrammarPath = maybe "bench/Memo.hpeg" id <$> lookupEnv "PEG_BENCH_LSP_GRAMMAR"

-- The stages of the checks that the language server runs on an edit
-- (ADR 0070), and one edit as a whole.
lspStages :: Text -> IO Benchmark
lspStages src = do
  let g0 = either (error . show) id (parseGrammar src)
      g = either (error . show) id (expandTemplates g0)
  _ <- evaluate (force (T.pack (show g)))
  -- A state with the document open and its outline computed, for the
  -- semantic tokens without the outline.
  let opened = stepState (handleMessage (stepState (handleMessage initialState initializeMsg)) (didOpenMsg src))
      tokensOf st = sum (map (B.length . encodeMessage) (stepOutput (handleMessage st semanticTokensMsg)))
  _ <- evaluate (tokensOf opened)
  let edited = sum . map (B.length . encodeMessage) . stepOutput
      parsed = parseFragments noFragments src
      table = parsedFragments parsed
  _ <- evaluate (length (show (parsedTops parsed, parsedOutline parsed)))
  pure $
    bgroup
      ("lsp (" <> show (length (T.lines src)) <> " lines)")
      $ [ bench "outline" (nf (\t -> T.pack (show (outline t))) src)
      , bench "parse" (nf (\t -> either (const 0) (length . show) (parseTops t)) src)
      , bench "parse and expand templates" (nf (\t -> either (const 0) (length . show) (parseGrammar t >>= expandTemplates)) src)
      , bench "check" (nf (either (const 0) (length . show) . check) g)
      , bench "label safety" (nf (length . show . labelWarnings) g)
      , bench "lint" (nf (length . show . lintGrammar) g0)
      , bench "semantic tokens (outline computed)" (nf tokensOf opened)
      , bench "semantic tokens (with the outline)" (nf (\t -> tokensOf (stepState (handleMessage opened (didChangeMsg 2 t)))) src)
      , bench "labels and recovery rules of the code actions" (nf (\t -> length (show (insertLabels [] t, recoverProposals t))) src)
      , bench "diagnose" (nf (length . show . diagnose) src)
      , bench "decode the didChange message (JSON)" (nf (\b -> maybe 0 (length . show) (J.parseJson b)) (J.renderJson (didChangeMsg 2 src)))
      , bench "an edit from its message: decode, check, encode" (nf (\b -> sum (map (B.length . encodeMessage) (stepOutput (handleFrame opened (Right b))))) (J.renderJson (didChangeMsg 2 src)))
      , bench "an edit: didChange and its diagnostics" (nf (\t -> sum (map (B.length . encodeMessage) (stepOutput (handleMessage opened (didChangeMsg 2 t))))) src)
      , bench "an edit and its semantic tokens" (nf (\t -> let s = handleMessage opened (didChangeMsg 2 t) in sum (map (B.length . encodeMessage) (stepOutput s)) + tokensOf (stepState s)) src)
      ]
        ++ concat
          [ [ bench ("an edit at the " <> place <> ", full text: decode, check, encode") (nf (edited . handleFrame opened . Right) (J.renderJson (didChangeMsg 2 new)))
            , bench ("an edit at the " <> place <> ", full text, and the semantic tokens") (nf (\b -> let s = handleFrame opened (Right b) in edited s + tokensOf (stepState s)) (J.renderJson (didChangeMsg 2 new)))
            , bench ("an edit at the " <> place <> ", range: decode, check, encode") (nf (edited . handleFrame opened . Right) (J.renderJson ranged))
            , bench ("an edit at the " <> place <> ", range, and the semantic tokens") (nf (\b -> let s = handleFrame opened (Right b) in edited s + tokensOf (stepState s)) (J.renderJson ranged))
            , bench ("an edit at the " <> place <> ": decode the range didChange (JSON)") (nf (\b -> maybe 0 (length . show) (J.parseJson b)) (J.renderJson ranged))
            , bench ("an edit at the " <> place <> ": parse by fragments") (nf (\t -> either (const 0) (length . show) (parsedTops (parseFragments table t))) new)
            , bench ("an edit at the " <> place <> ": outline by fragments") (nf (\t -> T.pack (show (parsedOutline (parseFragments table t)))) new)
            ]
          | place <- ["start", "middle", "end"]
          , let n = editLine place src
                new = insertLine n (T.pack "#") src
                ranged = rangeChangeMsg 2 (n, 0) (T.pack "#\n")
          ]

lspUri :: Text
lspUri = T.pack "file:///bench.hpeg"

lspMessage :: [(Text, J.Value)] -> J.Value
lspMessage fields = J.object ((T.pack "jsonrpc", J.String (T.pack "2.0")) : fields)

initializeMsg :: J.Value
initializeMsg = lspMessage [(T.pack "id", J.int 1), (T.pack "method", J.String (T.pack "initialize")), (T.pack "params", J.object [])]

didOpenMsg :: Text -> J.Value
didOpenMsg t =
  lspMessage
    [ (T.pack "method", J.String (T.pack "textDocument/didOpen"))
    , (T.pack "params", J.object [(T.pack "textDocument", J.object [(T.pack "uri", J.String lspUri), (T.pack "languageId", J.String (T.pack "peg")), (T.pack "version", J.int 1), (T.pack "text", J.String t)])])
    ]

didChangeMsg :: Int -> Text -> J.Value
didChangeMsg v t =
  lspMessage
    [ (T.pack "method", J.String (T.pack "textDocument/didChange"))
    , (T.pack "params", J.object [(T.pack "textDocument", J.object [(T.pack "uri", J.String lspUri), (T.pack "version", J.int v)]), (T.pack "contentChanges", J.Array [J.object [(T.pack "text", J.String t)]])])
    ]

semanticTokensMsg :: J.Value
semanticTokensMsg =
  lspMessage
    [ (T.pack "id", J.int 2)
    , (T.pack "method", J.String (T.pack "textDocument/semanticTokens/full"))
    , (T.pack "params", J.object [(T.pack "textDocument", J.object [(T.pack "uri", J.String lspUri)])])
    ]

-- The input of a session of the language server for timing peg-hs lsp
-- (ADR 0070): initialize, didOpen of a grammar, and 50 didChange of its
-- full text, each with one more comment line at the end, then shutdown and
-- exit. --lsp-session GRAMMAR OUT. In one file, the server reads the
-- changes faster than it checks them, and coalesces them.
lspSession :: FilePath -> FilePath -> IO ()
lspSession file out = B.writeFile out . B.concat . map encodeMessage =<< sessionMessages file

-- The messages of --lsp-session, one file each (DIR/000 ...), for sending
-- them one at a time: --lsp-messages GRAMMAR DIR.
lspMessages :: FilePath -> FilePath -> IO ()
lspMessages file dir = do
  msgs <- sessionMessages file
  forM_ (zip [0 :: Int ..] msgs) $ \(k, m) ->
    B.writeFile (dir </> reverse (take 3 (reverse ("00" <> show k)))) (encodeMessage m)

-- The places of the edits of ADR 0071: the line of the first, the middle
-- and the last definition of a rule (0-based).
editLine :: String -> Text -> Int
editLine place src =
  let defs = [i | (i, l) <- zip [0 ..] (T.lines src), T.pack " <- " `T.isInfixOf` l]
   in case place of
        "start" -> defs !! 0
        "middle" -> defs !! (length defs `div` 2)
        _ -> last defs

-- Insert a line before a line (0-based).
insertLine :: Int -> Text -> Text -> Text
insertLine n l src =
  let (a, b) = splitAt n (T.splitOn (T.pack "\n") src)
   in T.intercalate (T.pack "\n") (a ++ [l] ++ b)

-- A session that types into a new comment line before a definition
-- (ADR 0071): the first change inserts the line "#", and each later one an
-- x at its end. With the sync "full" the changes carry the full text, with
-- "range" only the inserted text and its range.
-- --lsp-session GRAMMAR OUT PLACE SYNC.
lspSessionAt :: String -> String -> FilePath -> FilePath -> IO ()
lspSessionAt place sync file out = B.writeFile out . B.concat . map encodeMessage =<< sessionMessagesAt place sync file

-- The messages of a session at a place, one file each:
-- --lsp-messages GRAMMAR DIR PLACE SYNC.
lspMessagesAt :: String -> String -> FilePath -> FilePath -> IO ()
lspMessagesAt place sync file dir = do
  msgs <- sessionMessagesAt place sync file
  forM_ (zip [0 :: Int ..] msgs) $ \(k, m) ->
    B.writeFile (dir </> reverse (take 3 (reverse ("00" <> show k)))) (encodeMessage m)

sessionMessagesAt :: String -> String -> FilePath -> IO [J.Value]
sessionMessagesAt place sync file = do
  src <- TIO.readFile file
  let n = editLine place src
      version k = insertLine n (T.pack "#" <> T.replicate (k - 2) (T.pack "x")) src
      change k
        | sync == "range" && k == 2 = rangeChangeMsg k (n, 0) (T.pack "#\n")
        | sync == "range" = rangeChangeMsg k (n, k - 2) (T.pack "x")
        | otherwise = didChangeMsg k (version k)
      shutdown = lspMessage [(T.pack "id", J.int 2), (T.pack "method", J.String (T.pack "shutdown"))]
      exit = lspMessage [(T.pack "method", J.String (T.pack "exit"))]
  pure ([initializeMsg, didOpenMsg src] ++ [change k | k <- [2 .. 51 :: Int]] ++ [shutdown, exit])

-- A didChange with one change of a range (TextDocumentSyncKind.Incremental,
-- ADR 0071): the text inserted at a position (0-based line and character).
rangeChangeMsg :: Int -> (Int, Int) -> Text -> J.Value
rangeChangeMsg v (l, c) t =
  lspMessage
    [ (T.pack "method", J.String (T.pack "textDocument/didChange"))
    , ( T.pack "params"
      , J.object
          [ (T.pack "textDocument", J.object [(T.pack "uri", J.String lspUri), (T.pack "version", J.int v)])
          , (T.pack "contentChanges", J.Array [J.object [(T.pack "range", J.object [(T.pack "start", pos), (T.pack "end", pos)]), (T.pack "text", J.String t)]])
          ]
      )
    ]
  where
    pos = J.object [(T.pack "line", J.int l), (T.pack "character", J.int c)]

sessionMessages :: FilePath -> IO [J.Value]
sessionMessages file = do
  src <- TIO.readFile file
  let edit k = src <> T.pack ("# edit " <> show k <> "\n")
      shutdown = lspMessage [(T.pack "id", J.int 2), (T.pack "method", J.String (T.pack "shutdown"))]
      exit = lspMessage [(T.pack "method", J.String (T.pack "exit"))]
  pure ([initializeMsg, didOpenMsg src] ++ [didChangeMsg k (edit k) | k <- [2 .. 51 :: Int]] ++ [shutdown, exit])

-- Memo table sizes and live memory, as material for choosing %nomemo rules
-- (ADR 0006, ADR 0017).
memoReport :: IO ()
memoReport = withArgs [] $ do
  let small = syntheticJson 1000
      (_, st) = JsonCounted.peg'parseWith Rt.defaultConfig {cfgCount = True} small
  putStrLn ("json, " <> show (T.length small) <> " characters: memo entries by rule")
  forM_ (sortOn (Down . snd) (M.toList (statsEntriesByRule st))) $ \(rule, k) ->
    putStrLn ("  " <> T.unpack rule <> ": " <> show k)
  forM_ [100, 200, 400] $ \n -> do
    let (_, pst) = Pathological.peg'parseWith Rt.defaultConfig {cfgCount = True} (pathological n)
    putStrLn $
      "pathological, n = " <> show n <> ": evaluations " <> show (sum (statsEvaluations pst))
        <> ", memo entries at the end " <> show (statsMemoEntries pst)

-- The peak live memory of one parse. The peak is per process, so each
-- variant runs in its own process: --memory
-- memoised|nomemo|syntax|syntax-tree|untyped-tree RECORDS.
memory :: String -> Int -> IO ()
memory "commonmark" _ = withArgs [] $ do
  input <- TIO.readFile specPath
  _ <- evaluate (T.length input)
  performMajorGC
  base <- getRTSStats
  r <- evaluate (either T.length T.length (CommonMark.toHtml input))
  performMajorGC
  stats <- getRTSStats
  putStrLn $
    "commonmark spec, " <> show (T.length input) <> " characters: output length " <> show r
      <> ", max live bytes " <> show (max_live_bytes stats)
      <> " (input and program before parsing: " <> show (max_live_bytes base) <> ")"
memory "lua" _ = withArgs [] $ do
  input <- luaSources
  _ <- evaluate (sum (map T.length input))
  performMajorGC
  base <- getRTSStats
  r <- evaluate (parseLua input)
  performMajorGC
  stats <- getRTSStats
  putStrLn $
    "lua test suite, " <> show (sum (map T.length input)) <> " characters: shown size " <> show r
      <> ", max live bytes " <> show (max_live_bytes stats)
      <> " (input and program before parsing: " <> show (max_live_bytes base) <> ")"
memory variant n = withArgs [] $ do
  let input = syntheticJson n
      run = case variant of
        "nomemo" -> either (const 0) (size . convertNomemo) . JsonNomemo.parse
        "syntax" -> either (const 0) (size . convertSyntax) . JsonSyntax.parse
        "syntax-tree" -> either (const 0) (snd . syntaxRange) . JsonSyntax.parseSyntax
        -- The grammar without type annotations and actions (ADR 0068).
        "untyped-tree" -> either (const 0) (snd . syntaxRange) . JsonUntyped.parseSyntax
        _ -> either (const 0) size . Json.parse
  _ <- evaluate (T.length input)
  performMajorGC
  base <- getRTSStats
  r <- evaluate (run input)
  performMajorGC
  stats <- getRTSStats
  putStrLn $
    "json, " <> show (T.length input) <> " characters, " <> variant <> ": tree size " <> show r
      <> ", max live bytes " <> show (max_live_bytes stats)
      <> " (input and program before parsing: " <> show (max_live_bytes base) <> ")"


convertNomemo :: JsonNomemo.Value -> Value
convertNomemo v = case v of
  JsonNomemo.Null -> Null
  JsonNomemo.Bool b -> Bool b
  JsonNomemo.Number t -> Number t
  JsonNomemo.String t -> String t
  JsonNomemo.Array vs -> Array (map convertNomemo vs)
  JsonNomemo.Object ms -> Object [(k, convertNomemo x) | (k, x) <- ms]

convertSyntax :: JsonSyntax.Value -> Value
convertSyntax v = case v of
  JsonSyntax.Null -> Null
  JsonSyntax.Bool b -> Bool b
  JsonSyntax.Number t -> Number t
  JsonSyntax.String t -> String t
  JsonSyntax.Array vs -> Array (map convertSyntax vs)
  JsonSyntax.Object ms -> Object [(k, convertSyntax x) | (k, x) <- ms]
