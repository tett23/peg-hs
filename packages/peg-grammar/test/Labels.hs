{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the label safety check (ADR 0028).
module Labels (labelTests) where

import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as M
import Data.Maybe (isNothing)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Check
import Peg.Grammar.Labels
import Peg.Grammar.Assemble (assemble)
import Peg.Grammar.Parser
import qualified SelfHostedNoLabels
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

labelTests :: [FilePath] -> TestTree
labelTests files =
  testGroup
    "label safety (ADR 0028)"
    [ testGroup "unsafe" [testCase (T.unpack n) (warnedLabels src @?= Right ["l"]) | (n, src) <- unsafeSnippets]
    , testGroup "safe" [testCase (T.unpack n) (warnedLabels src @?= Right []) | (n, src) <- safeSnippets]
    , testCase "indirect left recursion cannot be checked" $
        fmap (map (T.isInfixOf "cannot be checked")) (warningMessages indirect) @?= Right [True]
    , testCase "%safe silences the warning" $
        warnedLabels (grammar ["S :: ()", "S <- 'a' ('b' ^l) { () } / 'a' 'c' { () }", "%safe l"]) @?= Right []
    , testCase "%safe of a label that does not appear is an error" $
        fmap (const ()) (parseGrammar (grammar ["S :: ()", "S <- 'a' { () }", "%safe nolabel"]) >>= check)
          @?= Left [Diagnostic (Loc 4 1) "the label nolabel does not appear in the grammar"]
    , testCase "the grammars of the repository have no warnings" $ do
        ws <- mapM (\f -> (,) f . either (const []) labelWarnings . (>>= \g -> g <$ check g) <$> grammarOf f) files
        [(f, w) | (f, w) <- ws, not (null w)] @?= []
    , goldenVsString "the warnings" "test/golden/label-warnings.txt" $
        pure . BL.fromStrict . TE.encodeUtf8 . T.unlines $
          concat
            [ n : map ("  " <>) (either (map renderD) (map renderD) (warningsOf src))
            | (n, src) <- unsafeSnippets ++ [("indirect left recursion", indirect)]
            ]
    , testCase "the notation's grammar accepts the same language without its labels" $ do
        srcs <- mapM TIO.readFile files
        let differ =
              [ (f, m)
              | (f, src) <- zip files srcs
              , m <- mutants src
              , either (const Nothing) Just (parseGrammar m)
                  /= either (const Nothing) Just (either (const (Left [])) assemble (SelfHostedNoLabels.parse m))
              ]
        assertBool (show (length differ) <> " mutants differ, the first ones:\n" <> unlines [f <> ":\n" <> T.unpack m | (f, m) <- take 3 differ]) (null differ)
    , testProperty "a grammar without warnings accepts the same language without its labels" $
        withNumTests 3000 $
          forAll genGrammar $ \src -> case parseGrammar src >>= check >> parseGrammar src of
            Left _ -> discard
            Right g
              | not (null (labelWarnings g)) -> label "warned" True
              | not (hasLabels g) -> label "no labels" True
              | otherwise ->
                  let sameOn s = run True g s == run False g s || isNothing (run True g s) || isNothing (run False g s)
                      bad = filter (not . sameOn) inputs
                   in label "checked" (counterexample (T.unpack src <> "\ndiffers on " <> show (take 3 bad)) (null bad))
    ]
  where
    grammarOf f = parseGrammar <$> TIO.readFile f
    renderD (Diagnostic (Loc l c) m) = T.pack (show l) <> ":" <> T.pack (show c) <> ": " <> m

-- One character deleted or duplicated, at about 200 positions of a file.
mutants :: Text -> [Text]
mutants src =
  concat
    [ [T.take i src <> T.drop (i + 1) src, T.take (i + 1) src <> T.drop i src]
    | i <- [0, step .. T.length src - 1]
    ]
  where
    step = max 1 (T.length src `div` 100)

-- A grammar whose start rule S is defined by the given rules.
grammar :: [Text] -> Text
grammar rs = "%module M\n" <> T.unlines rs

unsafeSnippets :: [(Text, Text)]
unsafeSnippets =
  [ ("a later alternative with the same prefix", grammar ["S :: ()", "S <- 'a' ('b' ^l) { () } / 'a' 'c' { () }"])
  , ("a repetition followed by what it starts with", grammar ["S :: ()", "S <- ('x' ('y' ^l))* 'x' 'z' { () }"])
  , ("an optional whose failure lets the rest match", grammar ["S :: ()", "S <- ('a' ^l)? 'b' { () }"])
  , ("a failure in another rule", grammar ["S :: ()", "S <- A { () } / 'a' 'c' { () }", "A :: ()", "A <- 'a' ('b' ^l) { () }"])
  , ("the input can end", grammar ["S :: ()", "S <- 'a' ('b' ^l)? { () }"])
  , ( "the growth of left recursion stops"
    , grammar ["S :: ()", "S <- E '+' 'x' { () }", "E :: ()", "E <- E '+' (T ^l) { () } / T { () }", "T :: ()", "T <- [0-9] { () }"]
    )
  ]

safeSnippets :: [(Text, Text)]
safeSnippets =
  [ ("a later alternative with another first character", grammar ["S :: ()", "S <- 'a' ('b' ^l) { () } / 'c' { () }"])
  , ("a common prefix", grammar ["S :: ()", "S <- W 'a' ('b' ^l) { () } / W 'c' { () }", "W :: ()", "W <- ' '* { () }"])
  , ("a separator ends the repetition", grammar ["S :: ()", "S <- '[' V (',' (V ^l))* ']' { () }", "V :: ()", "V <- [0-9] { () }"])
  , ("the failure reaches the start rule", grammar ["S :: ()", "S <- A 'c' { () }", "A :: ()", "A <- 'a' ('b' ^l) { () }"])
  , ("the end of input is required", grammar ["S :: ()", "S <- (!. ^l) { () }"])
  , ("a label inside a lookahead", grammar ["S :: ()", "S <- &('a' ('b' ^l)) 'a' 'b' { () } / 'a' 'c' { () }"])
  , ( "left recursion whose growth cannot be followed by the operator"
    , grammar ["S :: ()", "S <- E { () }", "E :: ()", "E <- E '+' (T ^l) { () } / T { () }", "T :: ()", "T <- [0-9] { () }"]
    )
  ]

indirect :: Text
indirect = grammar ["S :: ()", "S <- A { () }", "A :: ()", "A <- B 'x' ('y' ^l) { () } / 'a' { () }", "B :: ()", "B <- A 'z' { () } / 'b' { () }"]

warningsOf :: Text -> Either [Diagnostic] [Diagnostic]
warningsOf src = do
  g <- parseGrammar src
  _ <- check g
  pure (labelWarnings g)

warningMessages :: Text -> Either [Text] [Text]
warningMessages src = either (Left . map diagMessage) (Right . map diagMessage) (warningsOf src)

-- The names of the labels with warnings.
warnedLabels :: Text -> Either [Text] [Text]
warnedLabels src = map (T.takeWhile (/= ' ') . T.drop (T.length "the label ")) <$> warningMessages src

hasLabels :: Grammar -> Bool
hasLabels g = any (any (any (exprHasLabel . itemExpr) . altItems) . ruleAlts) (grammarRules g)
  where
    exprHasLabel = \case
      ELabel {} -> True
      EGroup alts -> any (any (exprHasLabel . itemExpr)) alts
      EStar x -> exprHasLabel x
      EPlus x -> exprHasLabel x
      EOpt x -> exprHasLabel x
      EAnd x -> exprHasLabel x
      ENot x -> exprHasLabel x
      ECapture x -> exprHasLabel x
      _ -> False

-- An interpreter ---------------------------------------------------------------

data Res = Ok Int | Fail | Throw
  deriving (Eq, Show)

-- Whether the start rule matches the whole input, with or without labels.
-- 'Nothing' when the evaluation ran out of fuel.
run :: Bool -> Grammar -> String -> Maybe Bool
run withLabels g input = case grammarRules g of
  [] -> Nothing
  start : _ -> fmap (== Ok (length input)) (rule (ruleName start) 0 200)
  where
    rules = M.fromList [(ruleName r, r) | r <- grammarRules g]
    rule n i fuel
      | fuel <= (0 :: Int) = Nothing
      | otherwise = case M.lookup n rules of
          Just r -> choice (map altItems (ruleAlts r)) i (fuel - 1)
          Nothing -> Just Fail
    choice [] _ _ = Just Fail
    choice (a : as) i fuel =
      sequ a i fuel >>= \case
        Fail -> choice as i fuel
        r -> Just r
    sequ [] i _ = Just (Ok i)
    sequ (x : xs) i fuel =
      expr (itemExpr x) i fuel >>= \case
        Ok j -> sequ xs j fuel
        r -> Just r
    at i = if i < length input then Just (input !! i) else Nothing
    expr e i fuel = case e of
      ELit t _ -> Just (if T.unpack t == take (T.length t) (drop i input) then Ok (i + T.length t) else Fail)
      EClass rs _ -> Just (case at i of Just c | any (\(a, b) -> a <= c && c <= b) rs -> Ok (i + 1); _ -> Fail)
      EAny -> Just (if i < length input then Ok (i + 1) else Fail)
      ERef _ n _ -> rule n i fuel
      EGroup alts -> choice alts i fuel
      EStar x -> star x i fuel
      EPlus x ->
        expr x i fuel >>= \case
          Ok j -> star x j fuel
          r -> Just r
      EOpt x ->
        expr x i fuel >>= \case
          Fail -> Just (Ok i)
          r -> Just r
      EAnd x ->
        expr x i fuel >>= \case
          Ok _ -> Just (Ok i)
          _ -> Just Fail
      ENot x ->
        expr x i fuel >>= \case
          Ok _ -> Just Fail
          _ -> Just (Ok i)
      ECapture x -> expr x i fuel
      ELabel _ x _ ->
        expr x i fuel >>= \case
          Fail | withLabels -> Just Throw
          r -> Just r
      EPred _ _ -> Just (Ok i)
    star x i fuel =
      expr x i fuel >>= \case
        Ok j | j > i -> star x j fuel
        Ok _ -> Just (Ok i)
        Fail -> Just (Ok i)
        Throw -> Just Throw

inputs :: [String]
inputs = concatMap (\n -> sequence (replicate n "abc")) [0 .. 4]

-- Random grammars --------------------------------------------------------------

genGrammar :: Gen Text
genGrammar = do
  n <- choose (1, 3)
  bodies <- vectorOf n (genAlts n 3)
  -- Every rule is reachable from S.
  let reach = if n > 1 then " / 'c' " <> T.unwords (take (n - 1) ["A", "B"]) <> " { () }" else ""
  pure $
    grammar
      (concat [[name <> " :: ()", name <> " <- " <> b <> (if name == "S" then reach else "")] | (name, b) <- zip ["S", "A", "B"] bodies])

genAlts :: Int -> Int -> Gen Text
genAlts n d = do
  k <- choose (1, 3)
  alts <- vectorOf k (genSeq n d)
  pure (T.intercalate " / " [a <> " { () }" | a <- alts])

genSeq :: Int -> Int -> Gen Text
genSeq n d = do
  k <- choose (1, 3)
  T.unwords <$> vectorOf k (genExpr n d)

genExpr :: Int -> Int -> Gen Text
genExpr n d
  | d <= 0 = atom
  | otherwise =
      frequency
        [ (4, atom)
        , (1, (\x -> "(" <> x <> ")*") <$> genSeq n (d - 1))
        , (1, (\x -> "(" <> x <> ")?") <$> genSeq n (d - 1))
        , (1, (\x -> "(" <> x <> ")+") <$> genSeq n (d - 1))
        , (1, (\x -> "!(" <> x <> ")") <$> genSeq n (d - 1))
        , (1, (\x -> "&(" <> x <> ")") <$> genSeq n (d - 1))
        , (2, (\x y -> "(" <> x <> " / " <> y <> ")") <$> genSeq n (d - 1) <*> genSeq n (d - 1))
        , (3, (\x -> "(" <> x <> " ^l)") <$> genSeq n (d - 1))
        ]
  where
    atom =
      frequency
        [ (4, elements ["'a'", "'b'", "'c'"])
        , (1, elements ["[ab]", ".", "!."])
        , (2, elements (take n ["S", "A", "B"]))
        ]
