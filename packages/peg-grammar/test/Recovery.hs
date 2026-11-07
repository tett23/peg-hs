{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the syntax tree with error recovery for the language server
-- (ADR 0035).
module Recovery (recoveryTests) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Outline
import Peg.Grammar.Parser (parseTops)
import Control.Exception (SomeException, evaluate, try)
import Peg.Grammar.Parser (parseGrammar)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

recoveryTests :: [FilePath] -> TestTree
recoveryTests files =
  testGroup
    "syntax tree with recovery (ADR 0035)"
    -- One test per grammar file, so that they run in parallel (ADR 0039).
    [ testGroup
        "the tree of every mutant of the grammars is its text, and has its errors"
        [ testCase f $ do
            src <- TIO.readFile f
            let bad =
                  [ m
                  | m <- src : mutants src
                  , let o = outline m
                  , recoveredText m /= m || (either (const True) (const False) (parseTops m) && null (outlineSyntaxErrors o))
                  ]
            assertBool (show (length bad) <> " mutants, the first ones:\n" <> unlines (map T.unpack (take 2 bad))) (null bad)
        | f <- files
        ]
    -- The mutants above are at about 50 positions of each file. These are
    -- at any position; a failure shows the seed that finds it again
    -- (ADR 0081).
    , testProperty "the tree of a mutant at a random position is its text, and has its errors" $
        withNumTests 100 $ ioProperty $ do
          srcs <- mapM TIO.readFile files
          pure $
            forAll (elements (zip files srcs)) $ \(f, src) ->
              forAll (choose (0, max 0 (T.length src - 1))) $ \i ->
                forAll (elements [T.take i src <> T.drop (i + 1) src, T.take (i + 1) src <> T.drop i src]) $ \m ->
                  counterexample (f <> " at " <> show i) (recovers m)
    -- The grammar's parser and the parser with recovery end without an
    -- exception on any text, and the tree of the latter is the text
    -- (ADR 0035, ADR 0081).
    , testProperty "the parsers of the notation end on any text, and the recovered tree is the text" $
        forAll (T.pack <$> arbitrary) $ \t -> ioProperty $ do
          r <- try (evaluate (forceGrammar (parseGrammar t) `seq` (recoveredText t, length (show (outline t)))))
          pure $ case r of
            Left (e :: SomeException) -> counterexample (show e) False
            Right (text, n) -> n `seq` text === t
    , testCase "a valid grammar has no syntax errors" $ do
        srcs <- mapM TIO.readFile files
        [f | (f, src) <- zip files srcs, not (null (outlineSyntaxErrors (outline src)))] @?= []
    , testCase "breaking a rule leaves the other rules" $ do
        let names = map declName . outlineDeclarations . outline
        names broken @?= ["A", "A", "B", "B", "C", "C"]
        map (locLine . diagLoc) (outlineSyntaxErrors (outline broken)) @?= [7]
    , testCase "a line that is not a declaration is skipped" $
        map declName (outlineDeclarations (outline "%module M\n)))\nA :: ()\nA <- 'a' { () }\n")) @?= ["A", "A"]
    , testCase "the declarations and references of a grammar" $ do
        let o = outline "%module M\n%start A\n\nA :: ()\nA <- B<'x'> C { () }\n\nB<p> :: ()\nB<p> <- p { () }\n"
        [(declName d, declKind d, declTemplateParams d) | d <- outlineDeclarations o]
          @?= [("A", Annotation, Nothing), ("A", Definition, Nothing), ("B", Annotation, Just ["p"]), ("B", Definition, Just ["p"])]
        [(refName r, locLine (refStart r), locColumn (refStart r)) | r <- outlineReferences o] @?= [("B", 5, 6), ("C", 5, 13), ("p", 8, 9), ("A", 2, 8)]
    ]
  where
    recovers m = recoveredText m == m && not (either (const True) (const False) (parseTops m) && null (outlineSyntaxErrors (outline m)))
    forceGrammar = either (\ds -> length (show ds)) (\g -> length (show g))
    broken =
      T.unlines
        [ "%module M"
        , ""
        , "A :: ()"
        , "A <- B { () }"
        , ""
        , "B :: ()"
        , "B <- 'b' (C { () }"
        , ""
        , "C :: ()"
        , "C <- 'c' { () }"
        ]

-- One character deleted or duplicated, at about 50 positions of a file.
mutants :: T.Text -> [T.Text]
mutants src =
  concat
    [ [T.take i src <> T.drop (i + 1) src, T.take (i + 1) src <> T.drop i src]
    | i <- [0, step .. T.length src - 1]
    ]
  where
    step = max 1 (T.length src `div` 50)
