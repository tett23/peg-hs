{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the linter (ADR 0033).
module Lint (lintTests) where

import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Lint
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Data.List (intercalate, nub)
import Shard (chunkedProperty, chunks)

lintTests :: [FilePath] -> TestTree
lintTests files =
  testGroup
    "linter (ADR 0033)"
    ( [ testGroup "warns" [testCase (T.unpack n) (rulesOf src @?= Right [r]) | (n, r, src) <- warned]
    , testGroup "does not warn" [testCase (T.unpack n) (rulesOf src @?= Right []) | (n, src) <- notWarned]
    , goldenVsString "the warnings" "test/golden/lint-warnings.txt" $
        pure . BL.fromStrict . TE.encodeUtf8 . T.unlines $
          concat [n : map (("  " <>) . renderLintWarning "G.peg") (either (const []) id (lintOf src)) | (n, _, src) <- warned]
    , testCase "the grammars of the repository have no warnings" $ do
        ws <- mapM (\f -> (,) f . lintOf <$> TIO.readFile f) files
        [(f, w) | (f, w) <- ws, w /= Right []] @?= []
    ]
      ++ [ testGroup "the failures of the interpreter are those of peg-runtime (ADR 0049)" [testCase (T.unpack body <> " on " <> show input) (fmap renderFailure (run (grammarOf body) input) @?= Just message) | (body, input, message) <- runtimeErrors]
         , testCase "the comparison allows only the literal of the removed alternative to go (ADR 0049)" $ do
            let report xs = (Fail, Just (0, S.fromList xs))
            sameReport Nothing (report [XLit "'='", XLit "'=='"]) (report [XLit "'='"]) @?= False
            sameReport (Just "'=='") (report [XLit "'='", XLit "'=='"]) (report [XLit "'='"]) @?= True
            sameReport (Just "'=='") (report [XLit "'='", XLit "'=='", XLit "'a'"]) (report [XLit "'='"]) @?= False
            sameReport (Just "'=='") (report [XLit "'='"]) (report [XLit "'='", XLit "'=='"]) @?= False
            sameReport (Just "'=='") (Fail, Just (1, S.fromList [XLit "'='"])) (report [XLit "'='"]) @?= False
            sameReport Nothing (Ok 1, Nothing) (Fail, Nothing) @?= False
         ]
      ++ chunkedProperty "removing what a warning names keeps the results and the failure reports (ADR 0049)" 3000 (\part ->
          forAll (variant part genGrammar) $ \src -> case parseGrammar src of
            Right g | Right _ <- check g -> case [w | w <- lintGrammar g, lintRule w /= "unused-binding"] of
              [] -> label "no warnings" True
              ws ->
                label "warned" $
                  conjoin
                    [ counterexample (T.unpack src <> "\n" <> show w <> "\ndiffers on " <> show (take 3 bad)) (null bad)
                    | w <- ws
                    , let g' = fixed w g
                          removed = removedLiteral w g
                          bad = [s | s <- inputs, Just x <- [run g s], Just y <- [run g' s], not (sameReport removed x y)]
                    ]
            _ -> discard
        )
      ++ [ testCase "the parts of the split property check different grammars (ADR 0042)" $
            length (nub [unGen (variant part genGrammar) (mkQCGen 42) 30 | part <- [1 .. chunks]]) @?= chunks
         ]
    )

-- A grammar whose start rule S is defined by the given rules.
grammar :: [Text] -> Text
grammar rs = "%module M\n" <> T.unlines rs

lintOf :: Text -> Either [Diagnostic] [LintWarning]
lintOf src = do
  g <- parseGrammar src
  _ <- expandTemplates g >>= check
  pure (lintGrammar g)

rulesOf :: Text -> Either [Diagnostic] [Text]
rulesOf src = map lintRule <$> lintOf src

warned :: [(Text, Text, Text)]
warned =
  [ ("an alternative after an option", "unreachable-alternative", grammar ["S :: ()", "S <- 'a'? { () } / 'b' { () }"])
  , ("an alternative after a repetition and an empty sequence", "unreachable-alternative", grammar ["S :: ()", "S <- 'a'* 'c'? { () } / 'b' { () }"])
  , ("an alternative after an empty one", "unreachable-alternative", grammar ["S :: ()", "S <- 'a' { () } / { () } / 'b' { () }"])
  , ("a literal after its prefix", "unreachable-alternative", grammar ["S :: ()", "S <- '=' { () } / '==' 'x' { () }"])
  , ("the same literal again", "unreachable-alternative", grammar ["S :: ()", "S <- '=' { () } / '=' 'x' { () }"])
  , ("a duplicate alternative", "duplicate-alternative", grammar ["S :: ()", "S <- 'a' B { () } / 'c' { () } / 'a' B { () }", "B :: ()", "B <- 'b' { () }"])
  , ("a duplicate up to the bindings", "duplicate-alternative", grammar ["S :: Int", "S <- x:B 'a' { x } / y:B 'a' { y }", "B :: Int", "B <- 'b' { 1 }"])
  , ("a label in a lookahead", "ineffective-label", grammar ["S :: ()", "S <- &('a' ('b' ^l)) 'a' 'b' { () }"])
  , ("a label in the last alternative in a lookahead", "ineffective-label", grammar ["S :: ()", "S <- !('a' / 'b' ^l) 'c' { () }"])
  , ("a label in a nested lookahead", "ineffective-label", grammar ["S :: ()", "S <- !(!('a' ^l)) 'a' { () }"])
  , ("a binding not in the action", "unused-binding", grammar ["S :: ()", "S <- x:B { () }", "B :: Int", "B <- 'b' { 1 }"])
  , ("a binding that is only a part of another identifier", "unused-binding", grammar ["S :: Int", "S <- x:B { xs }", "B :: Int", "B <- 'b' { 1 }"])
  , ("a binding without an action", "unused-binding", grammar ["S :: Int", "S <- '(' x:B ')'", "B :: Int", "B <- 'b' { 1 }"])
  , ("a binding in a group", "unused-binding", grammar ["S :: ()", "S <- (x:B / 'c') { () }", "B :: ()", "B <- 'b' { () }"])
  ]

notWarned :: [(Text, Text)]
notWarned =
  [ ("an option that can throw", grammar ["S :: ()", "S <- ('a' ^l)? { () } / 'b' { () }"])
  , ("an option of a rule that can throw", grammar ["S :: ()", "S <- A? { () } / 'b' { () }", "A :: ()", "A <- 'a' ('b' ^l) { () }"])
  , ("an option followed by an item", grammar ["S :: ()", "S <- 'a'? 'c' { () } / 'b' { () }"])
  , ("an option that is not the whole alternative", grammar ["S :: ()", "S <- 'a' 'c'? { () } / 'b' { () }"])
  , ("a literal that is not a prefix", grammar ["S :: ()", "S <- '==' { () } / '=' { () }"])
  , ("a prefix followed by more", grammar ["S :: ()", "S <- '=' 'y' { () } / '==' { () }"])
  , ("a prefix under a label", grammar ["S :: ()", "S <- '=' { () } / ('==' ^l) { () }"])
  , ("alternatives that differ", grammar ["S :: ()", "S <- 'a' B { () } / 'a' C { () }", "B :: ()", "B <- 'b' { () }", "C :: ()", "C <- 'c' { () }"])
  , ("alternatives whose predicates read different bindings", grammar ["S :: ()", "S <- x:B y:C &{ x > y } { () } / y:B x:C &{ x > y } { () }", "B :: Int", "B <- 'b' { 1 }", "C :: Int", "C <- 'c' { 1 }"])
  , ("a label outside lookaheads", grammar ["S :: ()", "S <- 'a' ('b' ^l) { () }"])
  , ("a label in a choice in a lookahead", grammar ["S :: ()", "S <- !('a' ^l / 'b') 'c' { () }"])
  , ("a label in a repetition in a lookahead", grammar ["S :: ()", "S <- !(('a' ^l)*) 'c' { () }"])
  , ("a label in an option in a lookahead", grammar ["S :: ()", "S <- &(('a' ^l)? 'b') 'b' { () }"])
  , ("a binding in the action", grammar ["S :: Int", "S <- x:B { x }", "B :: Int", "B <- 'b' { 1 }"])
  , ("a binding in a predicate", grammar ["S :: ()", "S <- x:B &{ x > 0 } { () }", "B :: Int", "B <- 'b' { 1 }"])
  , ("a binding in an argument", grammar ["S :: ()", "S <- x:B C(x) { () }", "B :: Int", "B <- 'b' { 1 }", "C(n :: Int) :: ()", "C <- 'c' { () }"])
  , ("a binding in a string", grammar ["S :: String", "S <- x:B { \"x\" }", "B :: Int", "B <- 'b' { 1 }"])
  , ("a binding of a grammar with a syntax tree", "%module M\n%syntax\nS :: ()\nS <- x:B { () }\nB :: Int\nB <- 'b' { 1 }\n")
  , ("a binding that chooses the value", grammar ["S :: ()", "S <- Sp x:U Sp", "U :: ()", "U <- 'u' { () }", "Sp :: ()", "Sp <- ' '? { () }"])
  ]

-- The grammar without the alternative or the label a warning names.
fixed :: LintWarning -> Grammar -> Grammar
fixed w g = g {grammarRules = map rule (grammarRules g)}
  where
    rule r
      | lintRule w == "ineffective-label" = r {ruleAlts = [a {altItems = map item (altItems a)} | a <- ruleAlts r]}
      | otherwise = r {ruleAlts = [a | a <- ruleAlts r, altLoc a /= lintLoc w]}
    item i = i {itemExpr = expr (itemExpr i)}
    expr = \case
      ELabel l x n
        | l == lintLoc w -> expr x
        | otherwise -> ELabel l (expr x) n
      EGroup alts -> EGroup (map (map item) alts)
      EStar x -> EStar (expr x)
      EPlus x -> EPlus (expr x)
      EOpt x -> EOpt (expr x)
      EAnd x -> EAnd (expr x)
      ENot x -> ENot (expr x)
      ECapture x -> ECapture (expr x)
      e -> e

-- An interpreter ---------------------------------------------------------------

data Res = Ok Int | Fail | Throw
  deriving (Eq, Show)

-- What a failed terminal expected, as peg-runtime reports it: literals and
-- classes as written, any character, and the end of the input.
data Expect = XLit Text | XClass Text | XAny | XEnd
  deriving (Eq, Ord, Show)

-- The farthest position where a terminal failed, and what failed there.
type Failure = Maybe (Int, S.Set Expect)

-- Failures merge as in peg-runtime: the farther one wins, and at the same
-- position the expectations add up.
merge :: Failure -> Failure -> Failure
merge Nothing f = f
merge f Nothing = f
merge a@(Just (i, xs)) b@(Just (j, ys))
  | i > j = a
  | i < j = b
  | otherwise = Just (i, S.union xs ys)

-- The result of the start rule over the whole input, and the failure report.
-- As in peg-runtime, failures inside a negative lookahead and semantic
-- predicates are not reported, and a match that ends before the end of the
-- input expects the end there. 'Nothing' when the evaluation ran out of
-- fuel.
run :: Grammar -> String -> Maybe (Res, Failure)
run g input = case grammarRules g of
  [] -> Nothing
  start : _ ->
    rule (ruleName start) 0 200 >>= \case
      (Ok j, f) | j < length input -> Just (Fail, merge f (Just (j, S.singleton XEnd)))
      r -> Just r
  where
    rules = M.fromList [(ruleName r, r) | r <- grammarRules g]
    rule n i fuel
      | fuel <= (0 :: Int) = Nothing
      | otherwise = case M.lookup n rules of
          Just r -> choice (map altItems (ruleAlts r)) i (fuel - 1)
          Nothing -> Just (Fail, Nothing)
    choice [] _ _ = Just (Fail, Nothing)
    choice (a : as) i fuel =
      sequ a i fuel >>= \case
        (Fail, f) -> fmap (far f) (choice as i fuel)
        r -> Just r
    sequ [] i _ = Just (Ok i, Nothing)
    sequ (x : xs) i fuel =
      expr (itemExpr x) i fuel >>= \case
        (Ok j, f) -> fmap (far f) (sequ xs j fuel)
        r -> Just r
    far f (r, f') = (r, merge f f')
    terminal ok i j e = Just (if ok then (Ok j, Nothing) else (Fail, Just (i, S.singleton e)))
    expr e i fuel = case e of
      ELit t orig -> terminal (T.unpack t == take (T.length t) (drop i input)) i (i + T.length t) (XLit orig)
      EClass rs orig -> terminal (case drop i input of c : _ -> any (\(a, b) -> a <= c && c <= b) rs; [] -> False) i (i + 1) (XClass orig)
      EAny -> terminal (i < length input) i (i + 1) XAny
      ERef _ n _ -> rule n i fuel
      EGroup alts -> choice alts i fuel
      EStar x -> star x i fuel
      EPlus x ->
        expr x i fuel >>= \case
          (Ok j, f) -> fmap (far f) (star x j fuel)
          r -> Just r
      EOpt x ->
        expr x i fuel >>= \case
          (Fail, f) -> Just (Ok i, f)
          r -> Just r
      EAnd x -> fmap (\(r, f) -> (case r of Ok _ -> Ok i; _ -> Fail, f)) (expr x i fuel)
      ENot x -> fmap (\(r, _) -> (case r of Ok _ -> Fail; _ -> Ok i, Nothing)) (expr x i fuel)
      ECapture x -> expr x i fuel
      ELabel _ x _ ->
        expr x i fuel >>= \case
          (Fail, f) -> Just (Throw, f)
          r -> Just r
      EPred _ _ -> Just (Ok i, Nothing)
      EDiscard x -> expr x i fuel
      ETemplate {} -> Nothing
    star x i fuel =
      expr x i fuel >>= \case
        (Ok j, f) | j > i -> fmap (far f) (star x j fuel)
        (Ok _, f) -> Just (Ok i, f)
        (Fail, f) -> Just (Ok i, f)
        r -> Just r

-- The failure report as renderParseError writes it, for inputs of one line.
renderFailure :: (Res, Failure) -> String
renderFailure (_, f) = case f of
  Nothing -> "1:1: parse error"
  Just (i, xs) -> "1:" <> show (i + 1) <> ": " <> case map render (S.toAscList xs) of
    [] -> "parse error"
    [x] -> "expected " <> x
    ys -> "expected " <> intercalate ", " (init ys) <> " or " <> last ys
  where
    render = \case
      XLit t -> T.unpack t
      XClass t -> T.unpack t
      XAny -> "any character"
      XEnd -> "end of input"

-- Whether the grammar fixed by a warning reports the same as the original
-- (ADR 0049): the same result and farthest position, and the same
-- expectations, but for the first literal of an alternative removed by the
-- rule of literal prefixes, which may go.
sameReport :: Maybe Text -> (Res, Failure) -> (Res, Failure) -> Bool
sameReport removed (r, f) (r', f') =
  r == r' && fmap fst f == fmap fst f' && case (f, f') of
    (Just (_, xs), Just (_, ys)) ->
      ys `S.isSubsetOf` xs && (xs S.\\ ys) `S.isSubsetOf` maybe S.empty (S.singleton . XLit) removed
    _ -> True

-- The first literal of the alternative that a warning of a literal prefix
-- names.
removedLiteral :: LintWarning -> Grammar -> Maybe Text
removedLiteral w g
  | lintRule w == "unreachable-alternative" && "matches its prefix" `T.isInfixOf` lintMessage w =
      case [altItems a | r <- grammarRules g, a <- ruleAlts r, altLoc a == lintLoc w] of
        (x : _) : _ | ELit _ orig <- itemExpr x -> Just orig
        _ -> Nothing
  | otherwise = Nothing

-- Errors of peg-runtime, from peg-hs parse, for the grammar S <- BODY.
runtimeErrors :: [(Text, String, String)]
runtimeErrors =
  [ ("'a' 'b' { () } / 'a' 'c' { () }", "ax", "1:2: expected 'b' or 'c'")
  , ("'a' 'b' 'c' { () } / 'a' { () }", "abx", "1:3: expected 'c'")
  , ("&('a' 'b') 'a' 'x' { () } / 'z' { () }", "ac", "1:2: expected 'b'")
  , ("!('a' 'b') [a-z] [a-z] { () }", "ab", "1:1: parse error")
  , ("'=' { () } / '==' 'x' { () }", "", "1:1: expected '=' or '=='")
  , ("'=' { () }", "", "1:1: expected '='")
  , ("'a' { () }", "ab", "1:2: expected end of input")
  , ("[0-9] . { () }", "1", "1:2: expected any character")
  , ("'a' ('b' ^l) { () } / 'a' 'c' { () }", "ax", "1:2: expected 'b'")
  ]

grammarOf :: Text -> Grammar
grammarOf body = either (error . show) id (parseGrammar (grammar ["S :: ()", "S <- " <> body]))

inputs :: [String]
inputs = concatMap (\n -> sequence (replicate n "ab=")) [0 .. 3]

-- Random grammars with literals that are prefixes of others, options,
-- labels, lookaheads and repeated alternatives.
genGrammar :: Gen Text
genGrammar = do
  bodies <- vectorOf 2 genAlts
  pure (grammar (concat [[name <> " :: ()", name <> " <- " <> b <> (if name == "S" then " / 'b' A { () }" else "")] | (name, b) <- zip ["S", "A"] bodies]))
  where
    genAlts = do
      pool <- vectorOf 3 (genSeq 2)
      k <- choose (1, 4)
      alts <- vectorOf k (elements pool)
      pure (T.intercalate " / " [a <> " { () }" | a <- alts])
    genSeq d = do
      k <- choose (1, 3)
      T.unwords <$> vectorOf k (genExpr d)
    genExpr :: Int -> Gen Text
    genExpr d
      | d <= 0 = atom
      | otherwise =
          frequency
            [ (4, atom)
            , (1, (<> "?") <$> atom)
            , (1, (<> "*") <$> atom)
            , (1, (\e -> "(" <> e <> " ^l)") <$> genExpr (d - 1))
            , (1, ("&(" <>) . (<> ")") <$> genChoice (d - 1))
            , (1, ("!(" <>) . (<> ")") <$> genChoice (d - 1))
            , (1, ("(" <>) . (<> ")") <$> genChoice (d - 1))
            ]
    genChoice d = do
      k <- choose (1, 2)
      T.intercalate " / " <$> vectorOf k (genSeq d)
    atom = elements ["'a'", "'='", "'=='", "'=a'", "[ab]", "A"]
