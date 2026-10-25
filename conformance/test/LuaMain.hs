{-# LANGUAGE OverloadedStrings #-}

-- | Lua 5.5 conformance (ADR 0022), run against the official test suite of
-- Lua 5.5.1 and golden data made with the reference implementation
-- (lua/golden/regen.sh).
module Main (main) where

import Conformance.Lua.Ast (Block (..), Exp (..), Stat (..))
import Conformance.Lua.Eval (evaluate, renderValue, sexpr)
import qualified Conformance.Lua.Parser as Lua
import qualified Data.ByteString as B
import Data.Either (isLeft, isRight)
import Data.List (sort)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Codegen (Options (..), generateFromSource)
import Peg.Grammar.LabelInsertion (insertLabels)
import Peg.Runtime (renderParseError)
import Peg.Runtime.Internal (Config (..), Stats (..), defaultConfig)
import Peg.Runtime.Syntax (syntaxText)
import System.Directory (listDirectory)
import System.FilePath (takeExtension, (</>))
import Test.Tasty
import Test.Tasty.HUnit

dataDir :: FilePath
dataDir = "data/lua-5.5.1-tests"

-- Lua source is bytes: each byte becomes the code point of the same value.
-- A first line starting with '#' is dropped, keeping its newline, as
-- luaL_loadfilex does.
readSource :: FilePath -> IO Text
readSource name = prepare . TE.decodeLatin1 <$> B.readFile (dataDir </> name)

prepare :: Text -> Text
prepare t
  | "#" `T.isPrefixOf` t = T.dropWhile (/= '\n') t
  | otherwise = t

main :: IO ()
main = do
  files <- sort . filter ((== ".lua") . takeExtension) <$> listDirectory dataDir
  sources <- M.fromList <$> mapM (\f -> (,) f <$> readSource f) files
  traces <- golden "lua/golden/trace.tsv"
  evals <- golden "lua/golden/eval.tsv"
  mutations <- map (T.splitOn "\t") . T.lines <$> TIO.readFile "lua/golden/mutations.tsv"
  -- The reference implementation stops at the first error. When that is a
  -- semantic error, whether the rest of the file is free of syntax errors
  -- is unknown, so the case says nothing about the grammar.
  let checked = filter ((/= "semantic") . last) mutations
  defaultMain $
    testGroup
      "Lua 5.5 (ADR 0022)"
      [ testCase "the committed parser is up to date" regenerated
      , -- Every candidate of the grammar is next to Name, whose keyword check
        -- is a semantic predicate, or in left recursion: the label check
        -- shows none of them to be safe. The labelled grammar, and so its
        -- parser, is the grammar itself (ADR 0054).
        testCase "peg-hs label inserts no label, so the labelled parser is this parser (ADR 0054)" $ do
          src <- TIO.readFile "lua/Lua.hpeg"
          fmap fst (insertLabels [] src) @?= Right []
      , testGroup
          "accept: the official test suite"
          [testCase f (assertAccepts (sources M.! f)) | f <- files]
      , testCase ("structure: " <> show (length traces) <> " expressions traced by metamethods") $
          mismatches [(e, want, either (("error " <>) . renderParseError) sexpr (Lua.parseExp e)) | (e, want) <- traces]
      , testCase ("structure: " <> show (length evals) <> " expressions evaluated") $
          mismatches [(e, want, either (("error " <>) . renderParseError) (renderValue . evaluate) (Lua.parseExp e)) | (e, want) <- evals]
      , testCase ("reject: " <> show (length checked) <> " mutated files (" <> show (length mutations - length checked) <> " semantic errors not checked)") $
          mismatches [mutationResult sources m | m <- checked]
      , longBracketTests
      , globalTests
      , lexicalTests
      , testCase "lossless: the text of the tree is the input, for every file" $ do
          let bad = [f | (f, t) <- M.toList sources, fmap syntaxText (Lua.parseSyntax t) /= Right t]
          bad @?= []
      , testCase "complexity: memo entries and evaluations are linear in the input length" $ do
          let block = sources M.! "constructs.lua"
              body = T.unlines (filter (not . ("return" `T.isPrefixOf`)) (T.lines block))
              stats k = snd (Lua.peg'parseWith defaultConfig {cfgCount = True} (T.replicate k body))
              (s1, s4) = (stats 1, stats 4)
              evalsOf = sum . M.elems . statsEvaluations
              linear a b = fromIntegral b <= (4.4 :: Double) * fromIntegral a
          assertBool ("memo entries, 1 copy: " <> show (statsMemoEntries s1) <> ", 4 copies: " <> show (statsMemoEntries s4)) (linear (statsMemoEntries s1) (statsMemoEntries s4))
          assertBool ("evaluations, 1 copy: " <> show (evalsOf s1) <> ", 4 copies: " <> show (evalsOf s4)) (linear (evalsOf s1) (evalsOf s4))
      ]

golden :: FilePath -> IO [(Text, Text)]
golden path = map (\l -> let (a, b) = T.breakOn "\t" l in (a, T.drop 1 b)) . T.lines <$> TIO.readFile path

-- Fail with every mismatch listed.
mismatches :: [(Text, Text, Text)] -> Assertion
mismatches rs =
  case [(x, want, got) | (x, want, got) <- rs, want /= got] of
    [] -> pure ()
    bad -> assertFailure (show (length bad) <> " mismatches, the first ones:\n" <> unlines [T.unpack (x <> "\n  want: " <> want <> "\n  got:  " <> got) | (x, want, got) <- take 10 bad])

assertAccepts :: Text -> Assertion
assertAccepts t = case Lua.parse t of
  Right _ -> pure ()
  Left e -> assertFailure (T.unpack (renderParseError e))

-- A mutation line: file, kind, offsets, verdict.
mutationResult :: M.Map FilePath Text -> [Text] -> (Text, Text, Text)
mutationResult sources [file, kind, a, b, c, d, verdict] =
  let src = sources M.! T.unpack file
      num :: Text -> Int
      num = read . T.unpack
      (ia, ib, ic, id') = (num a, num b, num c, num d)
      piece x y = T.take (y - x) (T.drop x src)
      mutated = case kind of
        "duplicate" -> T.take ib src <> piece ia ib <> T.drop ib src
        "swap" -> T.take ia src <> piece ic id' <> piece ib ic <> piece ia ib <> T.drop id' src
        _ -> T.take ia src <> T.drop ib src
      want = if verdict == "accept" then "accept" else "reject"
      got = if isRight (Lua.parse mutated) then "accept" else "reject"
   in (T.intercalate " " [file, kind, a, b, c, d, verdict], want, got)
mutationResult _ l = (T.intercalate "\t" l, "a mutation line", "malformed")

accepts, rejects :: Text -> Assertion
accepts t = assertBool ("should accept: " <> T.unpack t) (isRight (Lua.parse t))
rejects t = assertBool ("should reject: " <> T.unpack t) (isLeft (Lua.parse t))

longBracketTests :: TestTree
longBracketTests =
  testGroup
    "long brackets"
    [ testCase "level 0" $ accepts "x = [[a]b]]"
    , testCase "level 1" $ accepts "x = [=[a]]b]=]"
    , testCase "level 3" $ accepts "x = [===[a]==]b]====]c]===]"
    , testCase "unmatched closing level" $ rejects "x = [==[a]=]"
    , testCase "unclosed" $ rejects "x = [[a"
    , testCase "first newline" $ accepts "x = [[\nline]]"
    , testCase "long comment" $ accepts "--[==[ a ]] ]=] ]==] x = 1"
    , testCase "unclosed long comment" $ rejects "--[[ x = 1"
    , testCase "a broken opening is a line comment" $ accepts "--[= x = 1\ny = 2"
    , testCase "call with a long string" $ accepts "f[[x]]"
    , testCase "an index is not a long string" $ accepts "x = t[ [[k]] ]"
    , testCase "an index followed by =" $ rejects "x = t[=1]"
    ]

globalTests :: TestTree
globalTests =
  testGroup
    "global"
    [ testCase "declaration" $ stats "global x" @?= Right [SGlobal Nothing [("x", Nothing)] []]
    , testCase "declaration with a value" $ accepts "global x, y = 1, 2"
    , testCase "attribute before the names" $ accepts "global <const> x, y"
    , testCase "attribute after a name" $ accepts "global x <const> = 1"
    , testCase "every name" $ stats "global *" @?= Right [SGlobalAll Nothing]
    , testCase "every name with an attribute" $ accepts "global <const> *"
    , testCase "function" $ accepts "global function f() end"
    , testCase "a variable named global" $ stats "global = 1" @?= Right [SAssign [EName "global"] [ENum "1"]]
    , testCase "a local named global" $ accepts "local global = 1"
    , testCase "read global" $ accepts "x = global"
    , testCase "a field of global" $ accepts "global.x = 1"
    , testCase "call global" $ accepts "global(x)"
    , testCase "declare a variable named global" $ stats "global global" @?= Right [SGlobal Nothing [("global", Nothing)] []]
    , testCase "global followed by a comparison is not a declaration" $ rejects "global <= 1"
    ]
  where
    stats t = either (Left . renderParseError) (\(Block ss _) -> Right ss) (Lua.parse t)

lexicalTests :: TestTree
lexicalTests =
  testGroup
    "lexical"
    [ testCase "hexadecimal float" $ accepts "x = 0x1.8p3 + 0X.1P-2 + 0xA"
    , testCase "decimal float" $ accepts "x = 1. + .5 + 3e2 + 3.E-2"
    , testCase "a numeral touching .." $ rejects "x = 1..2"
    , testCase "concatenation after a space" $ accepts "x = 1 .. 2"
    , testCase "a numeral touching a letter" $ rejects "x = 3x"
    , testCase "an exponent without digits" $ rejects "x = 1e"
    , testCase "hexadecimal without digits" $ rejects "x = 0x"
    , testCase "0xe+1 is 0xe plus 1" $ accepts "x = 0xe+1"
    , testCase "escapes" $ accepts "x = '\\a\\b\\f\\n\\r\\t\\v\\\\\\\"\\'\\x41\\65\\u{10FFFF}\\z  \n  x'"
    , testCase "an escaped newline" $ accepts "x = 'a\\\nb'"
    , testCase "an unescaped newline" $ rejects "x = 'a\nb'"
    , testCase "an invalid escape" $ rejects "x = '\\q'"
    , testCase "a decimal escape above 255" $ rejects "x = '\\256'"
    , testCase "a decimal escape of three digits then a digit" $ accepts "x = '\\1234'"
    , testCase "a UTF-8 escape below 2^31" $ accepts "x = '\\u{7FFFFFFF}'"
    , testCase "a UTF-8 escape of 2^31" $ rejects "x = '\\u{80000000}'"
    , testCase "leading zeros in a UTF-8 escape" $ accepts "x = '\\u{00000000041}'"
    , testCase "a hexadecimal escape needs two digits" $ rejects "x = '\\x4'"
    , testCase "an expression statement must be a call" $ rejects "a.b"
    , testCase "a call statement" $ accepts "a.b(c):d{}\"e\""
    , testCase "assignment to a call" $ rejects "f() = 1"
    , testCase "assignment to a parenthesised name" $ rejects "(a) = 1"
    , testCase "named vararg" $ accepts "function f(a, ...t) return t end"
    , testCase "return must end the block" $ rejects "return 1 x = 2"
    , testCase "a byte above 127 outside a string" $ rejects "x = 1 \xE9"
    , testCase "a byte above 127 in a string" $ accepts "x = '\xE9'"
    ]

regenerated :: Assertion
regenerated = do
  src <- TIO.readFile "lua/Lua.hpeg"
  committed <- B.readFile "lua/Conformance/Lua/Parser.hs"
  let opts = Options {optSourceName = "lua/Lua.hpeg", optOutputName = "lua/Conformance/Lua/Parser.hs", optDebugEntry = True, optExports = Nothing}
  case generateFromSource opts src of
    Left ds -> assertFailure (show ds)
    Right code -> assertBool "regenerate with scripts/regen-fixtures.sh" (TE.encodeUtf8 code == committed)
