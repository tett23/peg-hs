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
import Peg.Grammar.Templates (expandTemplates)
import qualified SelfHostedNoLabels
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Data.List (nub)
import Shard (chunkedProperty, chunks)

labelTests :: [FilePath] -> TestTree
labelTests files =
  testGroup
    "label safety (ADR 0028)"
    ( [ testGroup "unsafe" [testCase (T.unpack n) (warnedLabels src @?= Right ["l"]) | (n, src) <- unsafeSnippets]
    , testGroup "safe" [testCase (T.unpack n) (warnedLabels src @?= Right []) | (n, src) <- safeSnippets]
    , testCase "indirect left recursion cannot be checked" $
        fmap (map (T.isInfixOf "cannot be checked")) (warningMessages indirect) @?= Right [True]
    , testCase "%safe silences the warning" $
        warnedLabels (grammar ["S :: ()", "S <- 'a' ('b' ^l) { () } / 'a' 'c' { () }", "%safe l"]) @?= Right []
    , testCase "%safe of a label that does not appear is an error" $
        fmap (const ()) (parseGrammar (grammar ["S :: ()", "S <- 'a' { () }", "%safe nolabel"]) >>= check)
          @?= Left [Diagnostic (Loc 4 1) "the label nolabel does not appear in the grammar"]
    , testCase "the grammars of the repository have no warnings" $ do
        ws <- mapM (\f -> (,) f . fmap labelWarnings . (>>= \g -> g <$ check g) . (>>= expandTemplates) <$> grammarOf f) files
        [(f, w) | (f, w) <- ws, w /= Right []] @?= []
    , goldenVsString "the warnings" "test/golden/label-warnings.txt" $
        pure . BL.fromStrict . TE.encodeUtf8 . T.unlines $
          concat
            [ n : map ("  " <>) (either (map renderD) (map renderD) (warningsOf src))
            | (n, src) <- unsafeSnippets ++ [("indirect left recursion", indirect)]
            ]
    -- One test per grammar file, so that they run in parallel (ADR 0039).
    , testGroup
        "the notation's grammar accepts the same language without its labels"
        [ testCase f $ do
            src <- TIO.readFile f
            let differ =
                  [ m
                  | m <- mutants src
                  , either (const Nothing) Just (parseGrammar m)
                      /= either (const Nothing) Just (either (const (Left [])) assemble (SelfHostedNoLabels.parse m))
                  ]
            assertBool (show (length differ) <> " mutants differ, the first ones:\n" <> unlines (map T.unpack (take 3 differ))) (null differ)
        | f <- files
        ]
    , testGroup "precise in ADR 0038" [testCase (T.unpack n) (warnedLabels src @?= Right []) | (n, src) <- preciseSnippets]
    , testGroup "still unsafe in ADR 0038" [testCase (T.unpack n) (warnedLabels src @?= Right ["l"]) | (n, src) <- stillUnsafeSnippets]
    , testCase "the recovery rules become entries once each (ADR 0038)" $
        fmap (map unLoc . grammarEntries . stripLabelsAs "N") (parseGrammar sharedRecovery) @?= Right ["Skip"]
    , testCase "a rule named twice in %entry is an error (ADR 0038)" $
        fmap (const ()) (parseGrammar (grammar ["%entry A", "%entry A", "S :: ()", "S <- A { () }", "A :: ()", "A <- 'a' { () }"]) >>= check)
          @?= Left [Diagnostic (Loc 3 1) "the rule A is named in %entry twice"]
    ]
      ++ chunkedProperty "with parameters, constant predicates and long literals, a grammar without warnings accepts the same language without its labels (ADR 0038)" 3000 (\part ->
          forAll (variant part genGrammarWithParams) $ \src -> case parseGrammar src >>= check >> parseGrammar src of
            Left _ -> discard
            Right g
              | not (null (labelWarnings g)) -> label "warned" True
              | not (hasLabels g) -> label "no labels" True
              | otherwise ->
                  let sameOn s = run True g s == run False g s || isNothing (run True g s) || isNothing (run False g s)
                      bad = filter (not . sameOn) paramInputs
                   in label "checked" (counterexample (T.unpack src <> "\ndiffers on " <> show (take 3 bad)) (null bad))
        )
      ++ chunkedProperty "a grammar without warnings accepts the same language without its labels" 3000 (\part ->
          forAll (variant part genGrammar) $ \src -> case parseGrammar src >>= check >> parseGrammar src of
            Left _ -> discard
            Right g
              | not (null (labelWarnings g)) -> label "warned" True
              | not (hasLabels g) -> label "no labels" True
              | otherwise ->
                  let sameOn s = run True g s == run False g s || isNothing (run True g s) || isNothing (run False g s)
                      bad = filter (not . sameOn) inputs
                   in label "checked" (counterexample (T.unpack src <> "\ndiffers on " <> show (take 3 bad)) (null bad))
        )
      ++ [ testCase "the parts of a split property check different grammars (ADR 0042)" $ do
            let firsts g = [unGen (variant part g) (mkQCGen 42) 30 | part <- [1 .. chunks]]
            length (nub (firsts genGrammar)) @?= chunks
            length (nub (firsts genGrammarWithParams)) @?= chunks
         ]
    )
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
  , ("a repetition inside a negative lookahead", grammar ["S :: ()", "S <- !((('a' ^l) 'b')*) { () }"])
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

-- The shapes of the labels of Golem's grammar that the check of ADR 0028
-- warned about although they are safe (ADR 0038).
preciseSnippets :: [(Text, Text)]
preciseSnippets =
  [ ( "a common prefix through calls with the same arguments"
    , grammar
        [ "S :: ()"
        , "S <- B(0) 'x' { () }"
        , "B(n :: Int) :: ()"
        , "B <- Bad(n) { () } / Orphan(n) { () } / P(n) { () }"
        , "Bad(n :: Int) :: ()"
        , "Bad <- Ind(n) [ \\t] (&{ False })^l { () }"
        , "Orphan(n :: Int) :: ()"
        , "Orphan <- Ind(n) '=:' { () }"
        , "P(n :: Int) :: ()"
        , "P <- Ind(n) ![ \\t] 'p' { () }"
        , "Ind(n :: Int) :: ()"
        , "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
        ]
    )
  , ( "a later alternative that a constant predicate makes fail"
    , grammar
        [ "S :: ()"
        , "S <- I+ !. { () }"
        , "I :: ()"
        , "I <- C { () } / Bad { () } / T { () }"
        , "C :: ()"
        , "C <- '[' 'a' (']')^l { () }"
        , "Bad :: ()"
        , "Bad <- '[' &{ False } { () }"
        , "T :: ()"
        , "T <- [a-z]+ { () }"
        ]
    )
  , ( "the second character of a known prefix"
    , grammar
        [ "S :: ()"
        , "S <- E+ !. { () }"
        , "E :: ()"
        , "E <- Cm { () } / T { () }"
        , "Cm :: ()"
        , "Cm <- '%%' (!'%%' [a-z%])* ('%%')^l { () }"
        , "T :: ()"
        , "T <- (!'%%' [a-z%])+ { () }"
        ]
    )
  , ( "a known prefix against a rule that needs a letter"
    , grammar
        [ "S :: ()"
        , "S <- X+ !. { () }"
        , "X :: ()"
        , "X <- '[=' [0-9]+ (']')^l { () } / '[' Id ']' { () } / [a-z]+ { () }"
        , "Id :: ()"
        , "Id <- [a-z]+ { () }"
        ]
    )
  , ( "a known prefix from a rule of literals against a negative lookahead"
    , grammar
        [ "S :: ()"
        , "S <- A+ !. { () }"
        , "A :: ()"
        , "A <- Splat [a-z]+ (']')^l { () } / !Splat W { () }"
        , "Splat :: ()"
        , "Splat <- '**[' { () } / '*[' { () }"
        , "W :: ()"
        , "W <- [a-z*\\[]+ { () }"
        ]
    )
  ]

-- Shapes that the improvements of ADR 0038 must not take for safe.
stillUnsafeSnippets :: [(Text, Text)]
stillUnsafeSnippets =
  [ ( "calls with different arguments"
    , grammar
        [ "S :: ()"
        , "S <- B(0) 'x' { () }"
        , "B(n :: Int) :: ()"
        , "B <- Bad(n) { () } / Orphan(n + 1) { () }"
        , "Bad(n :: Int) :: ()"
        , "Bad <- Ind(n) [ \\t] (&{ False })^l { () }"
        , "Orphan(n :: Int) :: ()"
        , "Orphan <- Ind(n) '=:' { () }"
        , "Ind(n :: Int) :: ()"
        , "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
        ]
    )
  , ( "a binding that shadows a parameter"
    , grammar
        [ "S :: ()"
        , "S <- B(0) 'x' { () }"
        , "B(n :: Int) :: ()"
        , "B <- Bad(n) { () } / Orphan(n) { () }"
        , "Bad(n :: Int) :: ()"
        , "Bad <- n:Cnt Ind(n) [ \\t] (&{ False })^l { () }"
        , "Orphan(n :: Int) :: ()"
        , "Orphan <- Cnt Ind(n) '=:' { () }"
        , "Cnt :: Int"
        , "Cnt <- [0-9] { 0 }"
        , "Ind(n :: Int) :: ()"
        , "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
        ]
    )
  , ("a predicate that is not constant", grammar ["S :: ()", "S <- '[' 'a' (']')^l { () } / '[' &{ x } [a-z] { () }"])
  , ("a known prefix that the lookahead does not exclude", grammar ["S :: ()", "S <- '%' 'x' ('y')^l { () } / (!'%%' [%a-z])+ { () }"])
  , ( "a rule whose predicate reads the environment"
    , T.replace "%module M\n" "%module M\n%env Int\n" $
        grammar
          [ "S :: ()"
          , "S <- B(0) 'x' { () }"
          , "B(n :: Int) :: ()"
          , "B <- Bad(n) { () } / Orphan(n) { () }"
          , "Bad(n :: Int) :: ()"
          , "Bad <- Ind(n) [ \\t] (&{ False })^l { () }"
          , "Orphan(n :: Int) :: ()"
          , "Orphan <- &{ _env > 0 } Ind(n) '=:' { () }"
          , "Ind(n :: Int) :: ()"
          , "Ind <- &{ n == 0 } { () } / ' ' Ind(n - 1) { () }"
          ]
    )
  ]

-- Two labels with one recovery rule (ADR 0038).
sharedRecovery :: Text
sharedRecovery =
  grammar
    [ "%recover a Skip"
    , "%recover b Skip"
    , "S :: ()"
    , "S <- '(' ('x')^a (')')^b { () }"
    , "Skip :: ()"
    , "Skip <- (![)] .)* { () }"
    ]

indirect :: Text
indirect = grammar ["S :: ()", "S <- A { () }", "A :: ()", "A <- B 'x' ('y' ^l) { () } / 'a' { () }", "B :: ()", "B <- A 'z' { () } / 'b' { () }"]

warningsOf :: Text -> Either [Diagnostic] [Diagnostic]
warningsOf src = do
  g <- parseGrammar src >>= expandTemplates
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
      EDiscard x -> exprHasLabel x
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
      EPred b (Located _ c)
        | T.strip c == "False" -> Just (if b then Fail else Ok i)
        | T.strip c == "True" -> Just (if b then Ok i else Fail)
        | otherwise -> Just (Ok i)
      EDiscard x -> expr x i fuel
      ETemplate {} -> Nothing
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

-- Random grammars with parameters, constant predicates and literals of two
-- characters (ADR 0038). The predicates that are not constant succeed in the
-- interpreter; the check must not rely on their values.
genGrammarWithParams :: Gen Text
genGrammarWithParams = do
  s <- genAltsP False
  a <- genAltsP True
  b <- genAltsP True
  pure $
    grammar
      [ "S :: ()"
      , "S <- " <> s <> " / 'c' A(0) B(0) I(0) { () }"
      , "A(n :: Int) :: ()"
      , "A <- " <> a
      , "B(n :: Int) :: ()"
      , "B <- " <> b
      , "I(n :: Int) :: ()"
      , "I <- &{ n == 0 } { () } / ' ' I(n - 1) { () }"
      ]
  where
    genAltsP p = do
      k <- choose (1, 3)
      alts <- vectorOf k (genSeqP p (2 :: Int))
      pure (T.intercalate " / " [x <> " { () }" | x <- alts])
    genSeqP p d = do
      k <- choose (1, 3)
      T.unwords <$> vectorOf k (genExprP p d)
    genExprP p d
      | d <= 0 = atom p
      | otherwise =
          frequency
            [ (5, atom p)
            , (1, (\x -> "(" <> x <> ")*") <$> consuming)
            , (1, (\x -> "(" <> x <> ")?") <$> consuming)
            , (1, (\x -> "!(" <> x <> ")") <$> genSeqP p (d - 1))
            , (2, (\x y -> "(" <> x <> " / " <> y <> ")") <$> genSeqP p (d - 1) <*> genSeqP p (d - 1))
            , (3, (\x -> "(" <> x <> " ^l)") <$> genSeqP p (d - 1))
            ]
    -- Repetitions of expressions that match the empty string are errors.
    consuming = elements ["'a'", "' '", "'[='", "'%%'", "[a=]", "'a' I(0)"]
    atom p =
      frequency $
        [ (4, elements ["'a'", "' '", "'['", "'[='", "'%%'", "'%'", "'=a'"])
        , (1, elements ["[a=]", ".", "&{ False }", "&{ True }", "&{ x }", "!{ False }"])
        , (2, elements ["A(0)", "B(1)"])
        ]
          ++ [(3, elements ["I(n)", "A(n)", "B(n)", "A(n + 1)", "I(n - 1)"]) | p]

paramInputs :: [String]
paramInputs = concatMap (\n -> sequence (replicate n " a[=%")) [0 .. 4]

