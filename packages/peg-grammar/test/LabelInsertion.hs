{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Tests of inserting labels and proposing recovery rules (ADR 0054).
module LabelInsertion (labelInsertionTests) where

import qualified Data.ByteString.Lazy as BL
import Data.Either (isRight)
import Data.List (sort)
import Data.Maybe (isNothing)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Labels (genGrammar, grammar, indirect, inputs, preciseSnippets, run, safeSnippets, unsafeSnippets, warnedLabels)
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Format (formatGrammar)
import Peg.Grammar.LabelInsertion
import Peg.Grammar.Lint (LintWarning (..), lintGrammar)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import Shard (chunkedProperty)
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

labelInsertionTests :: [FilePath] -> TestTree
labelInsertionTests files =
  testGroup
    "label insertion (ADR 0054)"
    ( [ testGroup
          "candidates"
          [ testCase "the example of the ADR" $ do
              candidatesOf listExample @?= Right [("List", [(0, 1)], "Num"), ("List", [(0, 2), (0, 1)], "Num"), ("List", [(0, 3)], "rbracket")]
              fmap snd (insertLabels [] listExample) @?= Right listExampleLabelled
          , testCase "the example of a later alternative" $ do
              candidatesOf choiceExample @?= Right [("S", [(0, 1)], "b"), ("S", [(1, 1)], "c")]
              namesOf choiceExample @?= Right ["S_c"]
          , testCase "positions that are not candidates" $
              mapM_ (\(n, src) -> assertEqual (T.unpack n) (Right []) (candidatesOf src)) notCandidates
          , testCase "an item after one that matches the empty string" $
              candidatesOf (grammar ["S :: ()", "S <- 'a'? 'b' { () }"]) @?= Right []
          , testCase "not in an alternative that always succeeds for lint, and the rules it calls" $
              candidatesOf (grammar ["S :: ()", "S <- ('a' 'b')* B? { () } / 'c' 'd' { () }", "B :: ()", "B <- 'e' 'f' { () }"]) @?= Right [("S", [(1, 1)], "d")]
          , testCase "an item after a call of a template" $
              candidatesOf templateCall @?= Right [("S", [(0, 2)], "c")]
          ]
      , testGroup
          "selection"
          [ testGroup "the unsafe labels of ADR 0028 are not inserted" [testCase (T.unpack n) (insertedAtLabel src @?= Right False) | (n, src) <- unsafeSnippets]
          , testGroup
              "the safe labels of ADR 0028 and ADR 0038 are inserted"
              [ testCase (T.unpack n) (insertedAtLabel src @?= Right (n `notElem` notCandidateSnippets))
              | (n, src) <- safeSnippets ++ preciseSnippets
              ]
          , testCase "the safe examples insert labels" $
              length [() | (_, src) <- safeSnippets ++ preciseSnippets, insertedAtLabel src == Right True] @?= 9
          , testCase "nothing is inserted in growing alternatives of indirect left recursion" $
              fmap (map insertionRule . fst) (insertLabels [] (unlabel indirect)) @?= Right []
          ]
      , testGroup
          "covered positions"
          [ testCase "not inside a label with %recover and the rules it calls" $
              namesOf covered @?= Right ["S_z", "S_C", "S_D", "C_d", "D_w"]
          , testCase "the covered rules" $
              either (const []) id (fmap (sort . foldr (:) [] . coveredRules) (expanded covered)) @?= ["B", "E"]
          ]
      , testGroup
          "names"
          [ testCase "the targets" $
              map targetName
                [ ERef (Loc 1 1) "Expr" []
                , ERef (Loc 1 1) "Indent" [Located (Loc 1 1) "n"]
                , ELit "end" "'end'"
                , ELit ")" "')'"
                , ELit "]" "']'"
                , ELit "}" "'}'"
                , ELit "," "','"
                , ELit ";" "';'"
                , ELit "=" "'='"
                , ELit "::" "'::'"
                , ELit "a b" "'a b'"
                , EClass [('a', 'z')] "[a-z]"
                , EAny
                , EGroup []
                , EPlus (ELit "x" "'x'")
                , ECapture (EPlus (EClass [('0', '9')] "[0-9]"))
                ]
                @?= ["Expr", "Indent", "end", "rparen", "rbracket", "rbrace", "comma", "semi", "eq", "lit", "lit", "class", "any", "group", "x", "class"]
          , testCase "numbers from the second of a name, and around the names of the grammar" $
              namesOf numbered @?= Right ["S_B_2", "S_B_3", "S_C_2", "S_D_3", "S_X"]
          , testCase "the names are identifiers in the labelled grammar" $
              fmap (isRight . parseGrammar . snd) (insertLabels [] symbols) @?= Right True
          , testCase "the symbol names" $ do
              namesOf symbols @?= Right ["S_rparen", "S_rbracket", "S_rbrace", "S_comma", "S_semi", "S_eq", "S_lit", "S_class", "S_any", "S_group", "S_x", "S_A", "S_end"]
          ]
      , testGroup
          "rewriting"
          [ goldenVsString "comments, spaces, CRLF, bindings and captures" "test/golden/label-insertion.txt" $
              pure . BL.fromStrict . TE.encodeUtf8 $ case insertLabels [] messy of
                Left ds -> T.unlines (map diagMessage ds)
                Right (is, out) -> T.unlines ([showInsertion i | i <- is] ++ ["---"]) <> T.replace "\r" "<CR>" out
          , testCase "a rule given selects its candidates" $
              fmap (map insertionName . fst) (insertLabels ["C"] covered) @?= Right ["C_d"]
          , testCase "a rule that is not in the grammar is an error" $
              fmap fst (insertLabels ["Nope"] covered) @?= Left [Diagnostic (Loc 1 1) "undefined rule Nope"]
          , testCase "a grammar with an error inserts nothing" $
              fmap fst (insertLabels [] (grammar ["S :: ()", "S <- 'a' Missing { () }"])) @?= Left [Diagnostic (Loc 3 10) "undefined rule Missing"]
          , testCase "the grammars of the repository: inserting succeeds, and again inserts nothing" $ do
              rs <- mapM (\f -> (,) f . twice <$> TIO.readFile f) files
              [(f, r) | (f, r) <- rs, r /= Right []] @?= []
          ]
      ]
        ++ chunkedProperty "the text changes only by the labels inserted" 300 (\part ->
          forAll (variant part genPlain) $ \src -> case insertLabels [] src of
            Left _ -> discard
            Right (is, out) ->
              counterexample (T.unpack out) $
                applyEdits [Edit (insertionEnd i) (" ^" <> insertionName i) | i <- is] src === out
                  .&&. insertLabels [] src === Right (is, out)
                  .&&. fmap fst (insertLabels [] out) === Right []
        )
        ++ chunkedProperty "a formatted grammar stays formatted, and the warnings of lint stay" 300 (\part ->
          forAll (variant part genPlain) $ \gen -> case formatGrammar gen of
            Left _ -> discard
            Right src -> case insertLabels [] src of
              Left _ -> discard
              Right (_, out) ->
                counterexample (T.unpack out) $
                  formatGrammar out === Right out .&&. lintOf out === lintOf src
        )
        ++ chunkedProperty "the labelled grammar accepts the same language, and has no new warnings" 3000 (\part ->
          forAll (variant part genGrammar) $ \withLabels -> case insertLabels [] (unlabelAll withLabels) of
            Left _ -> discard
            Right ([], _) -> label "nothing inserted" True
            Right (is, out) -> case (parseGrammar (unlabelAll withLabels), parseGrammar out) of
              (Right g, Right g') ->
                let sameOn s = run False g s == run True g' s || isNothing (run False g s) || isNothing (run True g' s)
                    bad = filter (not . sameOn) inputs
                 in label "inserted" $
                      counterexample (T.unpack out <> "\ndiffers on " <> show (take 3 bad)) (null bad)
                        .&&. warnedLabels out === Right []
                        .&&. length is === length (labelsIn g')
              _ -> counterexample "not parsed again" False
        )
        ++ chunkedProperty "the warnings of the labels already there stay" 1000 (\part ->
          forAll (variant part genGrammar) $ \src -> case insertLabels [] src of
            Left _ -> discard
            Right (_, out) -> warnedLabels out === warnedLabels src
        )
    )
  where
    twice src = case insertLabels [] src of
      Left ds -> Left ds
      Right (_, out) -> fmap fst (insertLabels [] out)
    showInsertion i =
      let Loc l c = insertionStart i
          Loc l' c' = insertionEnd i
       in T.intercalate " " [T.pack (show l) <> ":" <> T.pack (show c), T.pack (show l') <> ":" <> T.pack (show c'), insertionRule i, insertionName i]

-- The rule, path and target of each candidate.
candidatesOf :: Text -> Either [Diagnostic] [(Text, [(Int, Int)], Text)]
candidatesOf src = do
  g0 <- parseGrammar src
  g <- expanded src
  pure [(candidateRule c, candidatePath c, targetName (candidateExpr c)) | c <- labelCandidates g0 g]

expanded :: Text -> Either [Diagnostic] Grammar
expanded src = parseGrammar src >>= expandTemplates >>= \g -> g <$ check g

-- The names of the labels inserted.
namesOf :: Text -> Either [Diagnostic] [Text]
namesOf src = map insertionName . fst <$> insertLabels [] src

lintOf :: Text -> [(Text, Int)]
lintOf src = either (const []) (map (\w -> (lintRule w, locLine (lintLoc w))) . lintGrammar) (parseGrammar src)

labelsIn :: Grammar -> [Text]
labelsIn g = concatMap (concatMap (concatMap (go . itemExpr) . altItems) . ruleAlts) (grammarRules g)
  where
    go = \case
      ELabel _ x l -> l : go x
      EGroup alts -> concatMap (concatMap (go . itemExpr)) alts
      EStar x -> go x
      EPlus x -> go x
      EOpt x -> go x
      EAnd x -> go x
      ENot x -> go x
      ECapture x -> go x
      EDiscard x -> go x
      _ -> []

-- The random grammars of the label check, without their labels.
genPlain :: Gen Text
genPlain = unlabelAll <$> genGrammar

unlabelAll :: Text -> Text
unlabelAll = T.replace " ^l)" ")"

-- A grammar with one label l, without it: the group around the labelled
-- expression is removed too, as in ('b' ^l) and (']')^l. The location is
-- where the expression starts.
unlabelAt :: Text -> (Text, Loc)
unlabelAt src =
  let (before, rest) = T.breakOn "^l" src
      afterLabel = T.drop 2 rest
      (o, inner, rest')
        | ")" `T.isSuffixOf` before =
            let o' = openOf (T.dropEnd 1 before)
             in (o', T.drop (o' + 1) (T.dropEnd 1 before), afterLabel)
        | otherwise =
            let o' = openOf before
             in (o', T.strip (T.drop (o' + 1) before), T.drop 1 (T.dropWhile (/= ')') afterLabel))
      out = T.take o before <> inner <> rest'
      prefix = T.take o before
      line = T.count "\n" prefix + 1
      col = T.length (snd (T.breakOnEnd "\n" prefix)) + 1
   in (out, Loc line col)
  where
    -- The offset of the parenthesis left open at the end of a text.
    openOf t = go (T.length t - 1) (0 :: Int)
      where
        go i depth
          | i < 0 = 0
          | otherwise = case T.index t i of
              ')' -> go (i - 1) (depth + 1)
              '(' | depth == 0 -> i
              '(' -> go (i - 1) (depth - 1)
              _ -> go (i - 1) depth

unlabel :: Text -> Text
unlabel = fst . unlabelAt

-- Whether a label is inserted where the label l of a snippet was.
insertedAtLabel :: Text -> Either [Diagnostic] Bool
insertedAtLabel src =
  let (plain, at) = unlabelAt src
   in any ((== at) . insertionStart) . fst <$> insertLabels [] plain

-- The safe snippets whose label, once removed, is not at a candidate: a
-- lookahead, a predicate, or an item inside a lookahead.
notCandidateSnippets :: [Text]
notCandidateSnippets = ["the end of input is required", "a label inside a lookahead", "a common prefix through calls with the same arguments"]

listExample :: Text
listExample =
  grammar
    [ "List :: [Int]"
    , "List <- '[' v:Num vs:(',' Num)* ']' !. { v : vs }"
    , ""
    , "Num :: Int"
    , "Num <- d:$[0-9]+ { read (unpack d) }"
    ]

listExampleLabelled :: Text
listExampleLabelled = T.replace "'[' v:Num vs:(',' Num)* ']' !." "'[' v:Num ^List_Num vs:(',' Num ^List_Num_2)* ']' ^List_rbracket !." listExample

choiceExample :: Text
choiceExample = grammar ["S :: ()", "S <- 'a' 'b' { () } / 'a' 'c' { () }"]

notCandidates :: [(Text, Text)]
notCandidates =
  [ ("the first item, repetitions, options, lookaheads, predicates and labels", grammar ["S :: ()", "S <- 'a' 'b'* 'c'? &'d' !'e' &{ True } 'f' ^x { () }"])
  , ("inside a lookahead", grammar ["S :: ()", "S <- 'a' &('b' 'c') !('d' 'e') 'f'* { () }"])
  , ("a recovery rule", grammar ["%recover r R", "S :: ()", "S <- ('a' ^r) { () }", "R :: ()", "R <- 'x' 'y' { () }"])
  , ("a template and the arguments of its call", grammar ["S :: ()", "S <- T<('a' 'b')> { () }", "T<p> :: ()", "T<p> <- 'x' p 'y' { () }"])
  , ("a reference and a group that match the empty string", grammar ["S :: ()", "S <- 'a' E ('b'? / 'c') { () }", "E :: ()", "E <- 'x'? { () }"])
  ]

templateCall :: Text
templateCall = grammar ["S :: ()", "S <- T<'a'> 'b'? 'c' { () }", "T<p> :: ()", "T<p> <- p { () }"]

covered :: Text
covered =
  grammar
    [ "%recover blk Skip"
    , "S :: ()"
    , "S <- 'a' B ^blk 'z' C D { () }"
    , "B :: ()"
    , "B <- 'b' E 'c' { () }"
    , "E :: ()"
    , "E <- 'e' 'f' { () }"
    , "C :: ()"
    , "C <- 'c' 'd' { () }"
    , "D :: ()"
    , "D <- 'x' ('y' 'w') ^nr { () }"
    , "Skip :: ()"
    , "Skip <- (!'z' .)* { () }"
    ]

numbered :: Text
numbered =
  grammar
    [ "%safe S_B"
    , "%recover S_C R"
    , "S :: ()"
    , "S <- 'a' B B C ('d' ^S_D) ^S_D_2 D { () } / 'z' X { () }"
    , "X :: ()"
    , "X <- 'q' 'x' ^S_B 'y' ^S_C { () }"
    , "B :: ()"
    , "B <- 'b' { () }"
    , "C :: ()"
    , "C <- 'c' { () }"
    , "D :: ()"
    , "D <- 'e' { () }"
    , "R :: ()"
    , "R <- { () }"
    ]

symbols :: Text
symbols = grammar ["S :: ()", "S <- 'a' ')' ']' '}' ',' ';' '=' '::' [a-z] . ('b' / 'c') 'x'+ $A+ 'end' !. { () }", "A :: ()", "A <- 'q' { () }"]

-- Comments, spaces, CRLF line breaks, bindings and captures.
messy :: Text
messy =
  T.intercalate
    "\r\n"
    [ "%module M"
    , "# a comment"
    , "S :: (Text, Text)"
    , "S <- '('   x:Word   # after an item"
    , "     ','  y:$( [a-z]+ )   ')'"
    , "       { (x, y) }"
    , ""
    , "Word :: Text"
    , "Word <- '<' w:$[a-z]+    '>' { w }"
    , ""
    ]
