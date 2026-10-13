{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the syntax tree with error recovery for the language server
-- (ADR 0035).
module Recovery (recoveryTests) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Outline
import Peg.Grammar.Parser (parseTops)
import Test.Tasty
import Test.Tasty.HUnit

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
