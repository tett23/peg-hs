{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import Peg.Runtime.Internal
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main =
  defaultMain $
    testGroup
      "peg-runtime"
      [ positionTests
      , errorTests
      , combinatorTests
      , memoTests
      , leftRecursionTests
      , columnTests
      ]

-- A store with no tables, for parsers that do not use rules.
data NoStore s = NoStore

parseWith :: Config -> (forall s. P (NoStore s) s a) -> Text -> Either ParseError a
parseWith cfg p t = fst (runParser cfg (pure NoStore) p t)

parse0 :: (forall s. P (NoStore s) s a) -> Text -> Either ParseError a
parse0 = parseWith defaultConfig

-- Positions --------------------------------------------------------------------

posAfter :: Text -> Text -> Pos
posAfter prefix rest =
  case parse0 (lit (T.unpack prefix) "p" >> spanFrom 0 >>= \s -> skipMany anyChar >> pure (spanEnd s)) (prefix <> rest) of
    Right p -> p
    Left e -> error (show e)

positionTests :: TestTree
positionTests =
  testGroup
    "positions"
    [ testCase "start of input" $ posAfter "" "x" @?= Pos 0 1 1
    , testCase "LF starts a line" $ posAfter "ab\n" "c" @?= Pos 3 2 1
    , testCase "CRLF: CR is the last character of the line" $ posAfter "ab\r" "\nc" @?= Pos 3 1 4
    , testCase "after CRLF" $ posAfter "ab\r\n" "c" @?= Pos 4 2 1
    , testCase "lone CR is not a newline" $ posAfter "a\rb" "c" @?= Pos 3 1 4
    , testCase "tab is one column" $ posAfter "\t\t" "x" @?= Pos 2 1 3
    , testCase "multibyte characters count once" $ posAfter "あい" "う" @?= Pos 6 1 3
    , testCase "astral plane character" $ posAfter "\x1F600" "x" @?= Pos 4 1 2
    , testCase "span of an alternative" $
        parse0 (lit "a\n" "a" >> getOffset >>= \o -> lit "bc" "bc" >> spanFrom o) "a\nbc"
          @?= Right (Span (Pos 2 2 1) (Pos 4 2 3))
    ]

-- Errors -----------------------------------------------------------------------

errorTests :: TestTree
errorTests =
  testGroup
    "errors"
    [ testCase "expected set at the farthest position" $
        fmap renderParseError (flipE (parse0 (lit "1" "'1'" >> choice [lit "+" "'+'", cls [('0', '9')] "[0-9]"]) "1*"))
          @?= Right "1:2: expected '+' or [0-9]"
    , testCase "a farther failure wins" $
        fmap (posOffset . parseErrorPos) (flipE (parse0 (choice [lit "ab" "'ab'" >> lit "c" "'c'", lit "a" "'a'" >> lit "x" "'x'"]) "abd"))
          @?= Right 2
    , testCase "leftover input expects the end" $
        fmap renderParseError (flipE (parse0 (lit "a" "'a'") "ab"))
          @?= Right "1:2: expected end of input"
    , testCase "failures inside a negative lookahead are not reported" $
        fmap (S.toList . parseErrorExpected) (flipE (parse0 (notP (lit "ab" "'ab'") >> lit "x" "'x'") "a"))
          @?= Right [ExpectedLiteral "'x'"]
    , testCase "predicate failures add nothing" $
        fmap (S.toList . parseErrorExpected) (flipE (parse0 (predicate (const False)) "a"))
          @?= Right []
    , testCase "expectations are ordered by kind, then text" $
        fmap (S.toList . parseErrorExpected) (flipE (parse0 (choice [anyChar >> anyChar, cls [('a', 'a')] "[a]", lit "z" "'z'"]) ""))
          @?= Right [ExpectedLiteral "'z'", ExpectedClass "[a]", ExpectedAny]
    , testCase "render with three expectations" $
        renderParseError (ParseError (Pos 0 3 7) (S.fromList [ExpectedLiteral "'a'", ExpectedLiteral "'b'", ExpectedEnd]) Nothing)
          @?= "3:7: expected 'a', 'b' or end of input"
    , testCase "render with no expectations" $
        renderParseError (ParseError (Pos 0 1 1) S.empty Nothing) @?= "1:1: parse error"
    ]

flipE :: Either a b -> Either b a
flipE = either Right Left

-- Combinators ------------------------------------------------------------------

combinatorTests :: TestTree
combinatorTests =
  testGroup
    "combinators"
    [ testCase "capture returns consumed text" $
        parse0 (capture (skipMany1 (cls [('0', '9')] "[0-9]"))) "123" @?= Right "123"
    , testCase "many collects" $
        parse0 (many (capture anyChar)) "abc" @?= Right ["a", "b", "c"]
    , testCase "optional" $
        parse0 (optional (lit "x" "x") >>= \m -> lit "y" "y" >> pure m) "y" @?= Right Nothing
    , testCase "andP consumes nothing" $
        parse0 (andP (lit "ab" "ab") >> capture (skipMany anyChar)) "ab" @?= Right "ab"
    , testCase "literal of any length matches by bytes" $
        parse0 (lit "あい" "'あい'") "あい" @?= Right ()
    , testCase "class matches a code point" $
        parse0 (cls [('ぁ', 'ん')] "[ぁ-ん]") "か" @?= Right ()
    ]

-- Memoisation ------------------------------------------------------------------

data Tree = Leaf Int | Add Tree Tree | Sub Tree Tree | Call Tree | Dot Tree
  deriving (Eq, Show)

-- A non-left-recursive grammar with heavy backtracking:
--   S <- A '!' / A '?' / A
--   A <- [0-9] A / [0-9]
data SA s = SA {tS :: Table s Int, tA :: Table s Int}

newSA :: ST s (SA s)
newSA = SA <$> newTable <*> newTable

ruleS :: P (SA s) s Int
ruleS =
  memo tS "S" $
    choice [ruleA >>= \a -> a <$ lit "!" "'!'", ruleA >>= \a -> a <$ lit "?" "'?'", ruleA]

ruleA :: P (SA s) s Int
ruleA =
  memo tA "A" $
    choice [cls [('0', '9')] "[0-9]" >> (+ 1) <$> ruleA, 1 <$ cls [('0', '9')] "[0-9]"]

runSA :: Config -> Text -> (Either ParseError Int, Stats)
runSA cfg = runParser cfg newSA ruleS

counting :: Config
counting = defaultConfig {cfgCount = True}

memoTests :: TestTree
memoTests =
  testGroup
    "memoisation"
    [ testCase "each rule body runs at most once per offset" $ do
        let (r, st) = runSA counting "12345?"
        r @?= Right 5
        assertBool "no rule evaluated twice" (all (<= 1) (M.elems (statsEvaluations st)))
    , testCase "memo entries equal the evaluated rule and offset pairs" $ do
        let (_, st) = runSA counting "12345?"
        statsMemoEntries st @?= M.size (statsEvaluations st)
    , testProperty "memoisation does not change results or errors" $
        forAll (listOf (elements "0123456789!?x")) $ \s ->
          let t = T.pack s
           in fst (runSA defaultConfig t) === fst (runSA defaultConfig {cfgMemo = False} t)
    ]

-- Left recursion ---------------------------------------------------------------

-- E <- E '+' N / E '-' N / N ; N <- [0-9]
data SE s = SE {tE :: Table s Tree, tN :: Table s Tree}

newSE :: ST s (SE s)
newSE = SE <$> newTable <*> newTable

ruleE :: P (SE s) s Tree
ruleE =
  memoLR tE "E" $
    choice
      [ do l <- ruleE; lit "+" "'+'"; Add l <$> ruleN
      , do l <- ruleE; lit "-" "'-'"; Sub l <$> ruleN
      , ruleN
      ]

ruleN :: P (SE s) s Tree
ruleN = memo tN "N" (Leaf . read . T.unpack <$> capture (cls [('0', '9')] "[0-9]"))

-- The indirect left recursion example of Medeiros et al.:
--   L <- P '.x' / 'x' ; P <- P '(n)' / L
data SL s = SL {tL :: Table s Tree, tP :: Table s Tree}

newSL :: ST s (SL s)
newSL = SL <$> newTable <*> newTable

ruleL :: P (SL s) s Tree
ruleL = memoLR tL "L" (choice [Dot <$> (ruleP <* lit ".x" "'.x'"), Leaf 0 <$ lit "x" "'x'"])

ruleP :: P (SL s) s Tree
ruleP = memoLR tP "P" (choice [Call <$> (ruleP <* lit "(n)" "'(n)'"), ruleL])

-- A rule that reads another left-recursive rule through a memoised helper:
--   X <- X 'b' / H ; H <- Y ; Y <- Y 'a' / 'a'
-- is not affected by discarding; the case below is:
--   A <- B 'c' / 'a' ; B <- C ; C <- A 'b'
-- where B and C are evaluated inside A's growth and memoised against a seed.
data SB s = SB {tA' :: Table s Text, tB :: Table s Text, tC :: Table s Text}

newSB :: ST s (SB s)
newSB = SB <$> newTable <*> newTable <*> newTable

ruleA' :: P (SB s) s Text
ruleA' = memoLR tA' "A" (choice [(<> "c") <$> (ruleB <* lit "c" "'c'"), "a" <$ lit "a" "'a'"])

ruleB :: P (SB s) s Text
ruleB = memoLR tB "B" ruleC

ruleC :: P (SB s) s Text
ruleC = memoLR tC "C" ((<> "b") <$> (ruleA' <* lit "b" "'b'"))

leftRecursionTests :: TestTree
leftRecursionTests =
  testGroup
    "left recursion"
    [ testCase "direct left recursion is left associative" $
        fst (runParser defaultConfig newSE ruleE "1-2+3")
          @?= Right (Add (Sub (Leaf 1) (Leaf 2)) (Leaf 3))
    , testCase "a single operand" $
        fst (runParser defaultConfig newSE ruleE "7") @?= Right (Leaf 7)
    , testCase "error after left recursion" $
        fmap renderParseError (flipE (fst (runParser defaultConfig newSE ruleE "1+")))
          @?= Right "1:3: expected [0-9]"
    , testCase "indirect left recursion (Medeiros et al.)" $
        fst (runParser defaultConfig newSL ruleL "x(n)(n).x(n).x")
          @?= Right (Dot (Call (Dot (Call (Call (Leaf 0))))))
    , testCase "a cycle through several rules" $
        fst (runParser defaultConfig newSB ruleA' "abcbc") @?= Right "abcbc"
    , testCase "memoisation off gives the same left-recursive result" $
        fst (runParser defaultConfig {cfgMemo = False} newSL ruleL "x(n).x")
          @?= fst (runParser defaultConfig newSL ruleL "x(n).x")
    , testCase "discarding matters: without it a stale seed is reused" $ do
        let with = fst (runParser defaultConfig newSB ruleA' "abcbc")
            without = fst (runParser defaultConfig {cfgDiscard = False} newSB ruleA' "abcbc")
        with @?= Right "abcbc"
        assertBool ("expected a different result without discarding, got " <> show without) (without /= with)
    ]

-- Columns ----------------------------------------------------------------------

colAfter :: Int -> Text -> Text -> Int
colAfter ts prefix rest =
  case parseWith defaultConfig {cfgTabstop = ts} (lit (T.unpack prefix) "p" >> withCol (\c -> c <$ skipMany anyChar)) (prefix <> rest) of
    Right c -> c
    Left e -> error (show e)

columnTests :: TestTree
columnTests =
  testGroup
    "columns"
    [ testCase "start of line is 0" $ colAfter 0 "ab\n" "c" @?= 0
    , testCase "without a tab stop a tab is one column" $ colAfter 0 "\t" "x" @?= 1
    , testCase "tab stop 4 from column 0" $ colAfter 4 "\t" "x" @?= 4
    , testCase "tab stop 4 from column 2" $ colAfter 4 "ab\t" "x" @?= 4
    , testCase "tab stop 4 from column 4" $ colAfter 4 "abcd\t" "x" @?= 8
    , testCase "multibyte character is one column" $ colAfter 4 "あ" "x" @?= 1
    , testCase "predicates see the column" $
        parseWith defaultConfig (lit "  " "s" >> predicate (== 2)) "  " @?= Right ()
    ]
