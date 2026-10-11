-- | CommonMark expressiveness probe (ADR 0011).
--
-- Runs all examples of spec 0.31.2 and checks, in both directions, that the
-- examples listed in commonmark/passing.txt are exactly the passing ones,
-- and that every failing example has a cause in commonmark/failures.txt.
--
-- Options:
--   --accept         rewrite passing.txt from the current results
--   --report FILE    write per-section results and failure causes as Markdown
--   --report-v1 FILE the same for the grammars without the ADR 0012
--                    extensions (the first snapshot of ADR 0011)
--   --show N         print the input, expected and actual output of example N
module Main (main) where

import qualified Conformance.CommonMark as CM
import Conformance.CommonMark.Emphasis (resolveEmphasis)
import Conformance.CommonMark.Types (Inline (..))
import Control.Monad (forM_, unless, when)
import qualified Data.ByteString as B
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Codegen (Options (..), generateFromSource)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Read (readMaybe)

data Example = Example
  { exNumber :: Int
  , exSection :: Text
  , exMarkdown :: Text
  , exHtml :: Text
  }

-- The example extraction of the spec's test runner, reimplemented.
extractExamples :: Text -> [Example]
extractExamples spec = go (1 :: Int) T.empty (T.lines spec)
  where
    fence = T.replicate 32 (T.pack "`")
    go _ _ [] = []
    go n section (l : ls)
      | T.strip l == fence <> T.pack " example" =
          let (md, rest) = break ((== T.pack ".") . T.strip) ls
              (html, rest') = break ((== fence) . T.strip) (drop 1 rest)
              ex = Example n section (unTab (T.unlines md)) (unTab (T.unlines html))
           in ex : go (n + 1) section (drop 1 rest')
      | T.isPrefixOf (T.pack "#") l, (hashes, title) <- T.span (== '#') l, not (T.null hashes), T.isPrefixOf (T.pack " ") title =
          go n (T.strip title) ls
      | otherwise = go n section ls
    unTab = T.replace (T.pack "\x2192") (T.pack "\t")

data Outcome = Pass | Fail Text

run :: Example -> Outcome
run = runWith CM.toHtml

runWith :: (Text -> Either Text Text) -> Example -> Outcome
runWith convert ex = case convert (exMarkdown ex) of
  Right html | html == exHtml ex -> Pass
  Right html -> Fail html
  Left err -> Fail (T.pack "parse failure: " <> err)

causes :: [Text]
causes = map T.pack ["indentation-state", "forward-reference", "tab-columns", "lookbehind", "rendering", "other"]

-- "number cause reason..." lines; '#' starts a comment.
readFailures :: IO (M.Map Int (Text, Text))
readFailures = do
  t <- TIO.readFile "commonmark/failures.txt"
  pure $
    M.fromList
      [ (n, (c, T.unwords reason))
      | l <- T.lines t
      , not (T.isPrefixOf (T.pack "#") (T.strip l))
      , num : c : reason <- [T.words l]
      , Just n <- [readMaybe (T.unpack num)]
      ]

readPassing :: IO (S.Set Int)
readPassing = do
  t <- TIO.readFile "commonmark/passing.txt"
  pure (S.fromList [n | w <- T.words t, Just n <- [readMaybe (T.unpack w)]])

main :: IO ()
main = do
  args <- getArgs
  spec <- TIO.readFile "data/commonmark-spec-0.31.2/spec.txt"
  let examples = extractExamples spec
      results = [(ex, run ex) | ex <- examples]
      passed = S.fromList [exNumber ex | (ex, Pass) <- results]
      failed = [ex | (ex, Fail _) <- results]
  case args of
    ["--show", n] | Just k <- readMaybe n -> forM_ [r | r@(ex, _) <- results, exNumber ex == k] showExample
    ["--accept"] -> do
      TIO.writeFile "commonmark/passing.txt" (T.unlines (map (T.pack . show) (S.toAscList passed)))
      putStrLn ("passing.txt: " <> show (S.size passed) <> " of " <> show (length examples))
    ["--report", file] -> readFailures >>= TIO.writeFile file . report examples results
    ["--report-v1", file] -> do
      failures <- readFailures
      let v1 = [(ex, runWith CM.toHtmlV1 ex) | ex <- examples]
          attributed = M.fromList [(exNumber ex, attribute failures ex) | (ex, Fail _) <- v1]
      TIO.writeFile file (report examples v1 attributed)
    _ -> do
      failures <- readFailures
      expected <- readPassing
      regenOk <- and <$> mapM regenerated ["Block", "Inline"]
      let problems =
            [T.pack ("expected 652 examples, found " <> show (length examples)) | length examples /= 652]
              ++ [T.pack ("example " <> show n <> " now passes; run with --accept") | n <- S.toList (passed `S.difference` expected)]
              ++ [T.pack ("example " <> show n <> " no longer passes") | n <- S.toList (expected `S.difference` passed)]
              ++ [T.pack ("example " <> show (exNumber ex) <> " fails without a cause in failures.txt") | ex <- failed, not (M.member (exNumber ex) failures)]
              ++ [T.pack ("failures.txt lists passing example " <> show n) | n <- M.keys failures, S.member n passed]
              ++ [T.pack ("unknown cause " <> T.unpack c <> " for example " <> show n) | (n, (c, _)) <- M.toList failures, c `notElem` causes]
              ++ [T.pack "regenerate the CommonMark parsers with scripts/regen-fixtures.sh" | not regenOk]
              ++ [ T.pack ("example " <> show n <> " should be in section " <> T.unpack s)
                 | (n, s) <- [(1, T.pack "Tabs"), (350, T.pack "Emphasis and strong emphasis"), (652, T.pack "Textual content")]
                 , [s] /= [exSection ex | ex <- examples, exNumber ex == n]
                 ]
              ++ emphasisProblems
      putStrLn ("CommonMark 0.31.2: " <> show (S.size passed) <> " of " <> show (length examples) <> " examples pass")
      unless (null problems) $ do
        mapM_ TIO.putStrLn problems
        exitFailure

regenerated :: String -> IO Bool
regenerated name = do
  let src = "commonmark/" <> name <> ".peg"
      out = "commonmark/Conformance/CommonMark/" <> name <> ".hs"
  grammar <- TIO.readFile src
  committed <- B.readFile out
  pure $ case generateFromSource (Options src out False) grammar of
    Right code -> TE.encodeUtf8 code == committed
    Left _ -> False

showExample :: (Example, Outcome) -> IO ()
showExample (ex, outcome) = do
  TIO.putStrLn (T.pack ("example " <> show (exNumber ex) <> " (" <> T.unpack (exSection ex) <> ")"))
  TIO.putStrLn (T.pack "--- markdown") >> TIO.putStr (exMarkdown ex)
  TIO.putStrLn (T.pack "--- expected") >> TIO.putStr (exHtml ex)
  case outcome of
    Pass -> TIO.putStrLn (T.pack "--- pass")
    Fail actual -> TIO.putStrLn (T.pack "--- actual") >> TIO.putStr actual >> when (not (T.isSuffixOf (T.pack "\n") actual)) (putStrLn "")

-- Markdown tables for the snapshot in docs/conformance/commonmark/.
report :: [Example] -> [(Example, Outcome)] -> M.Map Int (Text, Text) -> Text
report examples results failures =
  T.unlines $
    [ T.pack ("passing: " <> show total <> " / " <> show (length examples))
    , T.empty
    , T.pack "| section | pass | total |"
    , T.pack "|---|---:|---:|"
    ]
      ++ [ T.concat [T.pack "| ", s, T.pack " | ", tshow p, T.pack " | ", tshow t, T.pack " |"]
         | (s, (p, t)) <- sections
         ]
      ++ [ T.empty
         , T.pack "| cause | failing examples |"
         , T.pack "|---|---:|"
         ]
      ++ [ T.concat [T.pack "| ", c, T.pack " | ", tshow k, T.pack " |"]
         | c <- causes
         , let k = length [() | (_, (c', _)) <- M.toList failures, c' == c]
         , k > 0
         ]
      ++ [T.empty, T.pack "| example | section | cause | reason |", T.pack "|---:|---|---|---|"]
      ++ [ T.concat [T.pack "| ", tshow (exNumber ex), T.pack " | ", exSection ex, T.pack " | ", c, T.pack " | ", r, T.pack " |"]
         | (ex, Fail _) <- results
         , let (c, r) = M.findWithDefault (T.pack "?", T.empty) (exNumber ex) failures
         ]
  where
    total = length [() | (_, Pass) <- results]
    tshow :: Int -> Text
    tshow = T.pack . show
    order = M.fromListWith min [(exSection ex, exNumber ex) | ex <- examples]
    sections =
      sortOn (\(s, _) -> M.findWithDefault 0 s order) $
        M.toList $
          M.fromListWith
            (\(a, b) (c, d) -> (a + c, b + d))
            [(exSection ex, (case o of Pass -> 1; Fail _ -> 0, 1)) | (ex, o) <- results]

-- Unit tests of the emphasis post-processing on delimiter runs taken from
-- the spec's section on emphasis (ADR 0011).
emphasisProblems :: [Text]
emphasisProblems =
  [ T.pack ("emphasis post-processing of " <> show src <> " gave " <> show actual)
  | (src, toks, expected) <- cases
  , let actual = resolveEmphasis (T.pack src) toks
  , actual /= expected
  ]
  where
    s = Str . T.pack
    cases =
      [ ("*foo bar*", [Delim '*' 1 0 1, s "foo bar", Delim '*' 1 8 9], [Emph [s "foo bar"]])
      , ("a * foo bar*", [s "a ", Delim '*' 1 2 3, s " foo bar", Delim '*' 1 11 12], [s "a ", s "*", s " foo bar", s "*"])
      , ("**foo**", [Delim '*' 2 0 2, s "foo", Delim '*' 2 5 7], [Strong [s "foo"]])
      , ("***foo***", [Delim '*' 3 0 3, s "foo", Delim '*' 3 6 9], [Emph [Strong [s "foo"]]])
      , ("foo*bar*", [s "foo", Delim '*' 1 3 4, s "bar", Delim '*' 1 7 8], [s "foo", Emph [s "bar"]])
      , ("foo_bar_", [s "foo", Delim '_' 1 3 4, s "bar", Delim '_' 1 7 8], [s "foo", s "_", s "bar", s "_"])
      , ("*foo**bar*", [Delim '*' 1 0 1, s "foo", Delim '*' 2 4 6, s "bar", Delim '*' 1 9 10], [Emph [s "foo", s "**", s "bar"]])
      ]

-- Causes for the failures of the v1 grammars, assigned by rule rather than
-- by hand: the recorded cause if the example fails with the extensions too,
-- otherwise by what the example contains.
attribute :: M.Map Int (Text, Text) -> Example -> (Text, Text)
attribute failures ex
  | Just c <- M.lookup (exNumber ex) failures = c
  | any isRefDef ls = (T.pack "forward-reference", T.pack "参照定義を含む")
  | any isContainerLine ls = (T.pack "indentation-state", T.pack "引用かリスト項目を含む")
  | T.any (== '\t') md = (T.pack "tab-columns", T.pack "タブを含む")
  | otherwise = (T.pack "other", T.pack "v1 の近似（長さや字下げの比較）")
  where
    md = exMarkdown ex
    ls = T.lines md
    isRefDef l = case T.uncons (T.stripStart l) of
      Just ('[', rest) -> T.isInfixOf (T.pack "]:") rest
      _ -> False
    isContainerLine l =
      let t = T.stripStart l
       in T.isPrefixOf (T.pack ">") t
            || any (\m -> T.isPrefixOf (T.pack m) t) ["- ", "+ ", "* ", "-\t"]
            || t `elem` map T.pack ["-", "+", "*"]
            || orderedMarker t
    orderedMarker t =
      let (ds, rest) = T.span (`elem` ['0' .. '9']) t
       in not (T.null ds) && T.length ds <= 9 && (T.isPrefixOf (T.pack ".") rest || T.isPrefixOf (T.pack ")") rest)
