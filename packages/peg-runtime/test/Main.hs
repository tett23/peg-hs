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
      , recoveryTests
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
    , testGroup
        "discarding only seed dependents (ADR 0024)"
        [ sameAsDiscardAll "indirect (Medeiros et al.)" "x(n)." newSL ruleL
        , sameAsDiscardAll "a cycle through several rules" "abc" newSB ruleA'
        , sameAsDiscardAll "direct" "0123456789+-" newSE ruleE
        , sameAsDiscardAll "nested levels" "x+*^()" newSX ruleX1
        , testProperty "recovery gives the same values and errors" $
            forAll (T.pack <$> listOf (elements "0123456789+ ")) $ \t ->
              let run c = (\(v, e, _) -> (show v, ranges e)) (runParserRecover c newSN ruleE' t)
               in run defaultConfig === run defaultConfig {cfgDiscardAll = True}
        , testCase "nested left recursion: evaluations are linear in the nesting depth" $ do
            let evals d = sum (M.elems (statsEvaluations (snd (runParser defaultConfig {cfgCount = True} newSX ruleX1 (nested d)))))
            fst (runParser defaultConfig newSX ruleX1 (nested 3)) @?= Right ()
            assertBool ("depth 8: " <> show (evals 8) <> ", depth 16: " <> show (evals 16)) (fromIntegral (evals 16) <= (2.5 :: Double) * fromIntegral (evals 8))
        ]
    ]
  where
    nested d = T.replicate d "(" <> "x" <> T.replicate d ")"

-- The results, failures and statistics other than counts agree with the
-- uniform discarding of ADR 0013.
sameAsDiscardAll :: (Show a) => String -> String -> (forall s. ST s (store s)) -> (forall s. P (store s) s a) -> TestTree
sameAsDiscardAll name alphabet mk rule =
  testProperty name $
    forAll (T.pack <$> listOf (elements alphabet)) $ \t ->
      show (fst (runParser defaultConfig mk rule t)) === show (fst (runParser defaultConfig {cfgDiscardAll = True} mk rule t))

-- Three nested left-recursive levels:
--   X1 <- X1 '+' X2 / X2 ; X2 <- X2 '*' X3 / X3 ; X3 <- X3 '^' A / A
--   A <- 'x' / '(' X1 ')'
data SX s = SX {tX1 :: Table s (), tX2 :: Table s (), tX3 :: Table s (), tXA :: Table s ()}

newSX :: ST s (SX s)
newSX = SX <$> newTable <*> newTable <*> newTable <*> newTable

ruleX1, ruleX2, ruleX3, ruleXA :: P (SX s) s ()
ruleX1 = memoLR tX1 "X1" (choice [ruleX1 >> lit "+" "'+'" >> ruleX2, ruleX2])
ruleX2 = memoLR tX2 "X2" (choice [ruleX2 >> lit "*" "'*'" >> ruleX3, ruleX3])
ruleX3 = memoLR tX3 "X3" (choice [ruleX3 >> lit "^" "'^'" >> ruleXA, ruleXA])
ruleXA = memo tXA "A" (choice [lit "x" "'x'", lit "(" "'('" >> ruleX1 >> lit ")" "')'"])

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

-- Labelled failures and recovery (ADR 0021) ----------------------------------

recover0 :: (forall s. P (NoStore s) s a) -> Text -> (Maybe a, [SyntaxError])
recover0 p t = let (v, e, _) = runParserRecover defaultConfig (pure NoStore) p t in (v, e)

ranges :: [SyntaxError] -> [(Maybe Text, (Int, Int))]
ranges = map (\e -> (syntaxErrorLabel e, syntaxErrorRange e))

-- Skip to the next ';' and consume it.
toSemi :: P r s Text
toSemi = "?" <$ (skipMany (cls [('\0', ':'), ('<', '\x10FFFF')] "[^;]") >> lit ";" "';'")

-- The label is only reached when input remains: at the end of the input,
-- failing is the normal end of the repetition and must not throw.
stmt :: P r s Text
stmt = andP anyChar >> labeled "stmt" (Just toSemi) (capture (lit "ok;" "'ok;'"))

-- S <- Stmt* ; Stmt <- 'ok;' ^stmt, memoised
data SR s = SR {tStmt :: Table s Text, tStmts :: Table s [Text]}

newSR :: ST s (SR s)
newSR = SR <$> newTable <*> newTable

ruleS' :: P (SR s) s [Text]
ruleS' = memo tStmts "S" (many ruleStmt)

ruleStmt :: P (SR s) s Text
ruleStmt = memo tStmt "Stmt" stmt

-- E <- E '+' (N ^num) / N, recovering a number by skipping to the next '+'
data SN s = SN {tE' :: Table s Tree, tN' :: Table s Tree}

newSN :: ST s (SN s)
newSN = SN <$> newTable <*> newTable

ruleE' :: P (SN s) s Tree
ruleE' =
  memoLR tE' "E" $
    choice
      [ do l <- ruleE'; lit "+" "'+'"; Add l <$> labeled "num" (Just (Leaf (-1) <$ skipMany1 (cls [('\0', '*'), (',', '\x10FFFF')] "[^+]"))) ruleN'
      , ruleN'
      ]

ruleN' :: P (SN s) s Tree
ruleN' = memo tN' "N" (Leaf . read . T.unpack <$> capture (cls [('0', '9')] "[0-9]"))

recoveryTests :: TestTree
recoveryTests =
  testGroup
    "labelled failures and recovery (ADR 0021)"
    [ testCase "choice does not catch a thrown label" $
        fmap parseErrorLabel (flipE (parse0 (choice [labeled "x" Nothing (lit "a" "'a'"), lit "b" "'b'"]) "b"))
          @?= Right (Just "x")
    , testCase "a label thrown inside a lookahead is an ordinary failure" $
        parse0 (notP (labeled "x" Nothing (lit "a" "'a'")) >> lit "b" "'b'") "b" @?= Right ()
    , testCase "without recovery the parse fails with the label" $
        fmap parseErrorLabel (flipE (parse0 (many stmt) "ok;bad;ok;")) @?= Right (Just "stmt")
    , testCase "recovery skips to the synchronisation point" $ do
        let (v, errs) = recover0 (many stmt) "ok;bad;ok;"
        v @?= Just ["ok;", "?", "ok;"]
        ranges errs @?= [(Just "stmt", (3, 7))]
        map (S.toList . syntaxErrorExpected) errs @?= [[ExpectedLiteral "'ok;'"]]
    , testCase "a recovery that consumes nothing records an empty range" $ do
        let close = labeled "close" (Just (pure ())) (lit "]" "']'")
            (v, errs) = recover0 (lit "[a" "'[a'" >> close >> capture (skipMany anyChar)) "[a b"
        v @?= Just " b"
        ranges errs @?= [(Just "close", (2, 2))]
    , testCase "errors of an abandoned attempt are not reported" $ do
        let first = labeled "l" (Just ("x" <$ skipMany1 (cls [('x', 'x')] "x"))) (capture (lit "a" "'a'")) <* lit "!" "'!'"
            (v, errs) = recover0 (choice [first, capture (lit "xx?" "'xx?'")]) "xx?"
        v @?= Just "xx?"
        errs @?= []
    , testCase "an unrecoverable start rule makes the whole input an error" $ do
        let (v, errs) = recover0 (labeled "x" Nothing (lit "a" "'a'")) "bc"
        v @?= Nothing
        ranges errs @?= [(Just "x", (0, 2))]
    , testCase "left over input is an error" $ do
        let (v, errs) = recover0 (lit "a" "'a'") "abc"
        v @?= Just ()
        ranges errs @?= [(Nothing, (1, 3))]
    , testCase "memoisation does not change recovered results" $
        mapM_
          ( \t ->
              let run cfg = let (v, e, _) = runParserRecover cfg newSR ruleS' t in (v, e)
               in run defaultConfig {cfgMemo = False} @?= run defaultConfig
          )
          ["ok;bad;ok;", "bad;bad;", "ok;", "", "ok;x", "x;ok;y;"]
    , testCase "recovery inside left recursion keeps the tree left associative" $ do
        let (v, errs, _) = runParserRecover defaultConfig newSN ruleE' "1+x+2"
        v @?= Just (Add (Add (Leaf 1) (Leaf (-1))) (Leaf 2))
        ranges errs @?= [(Just "num", (2, 3))]
    ]
