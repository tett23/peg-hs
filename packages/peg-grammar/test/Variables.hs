{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the lexical reading of the variables of Haskell code
-- (ADR 0082).
module Variables (variableTests) where

import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

variableTests :: TestTree
variableTests =
  testGroup
    "the variables of Haskell code (ADR 0082)"
    [ testGroup "reads" [testCase (T.unpack code) (names code @?= expected) | (code, expected) <- reads']
    , testCase "the locations start at the location of the code" $
        codeVariables (Loc 0 3 8) " y > 0 " @?= [Located (Loc 0 3 9) "y"]
    , testCase "a name on a later line is at its column of that line" $
        codeVariables (Loc 0 3 13) "case s of\n    _ -> f s\n  " @?= [Located (Loc 0 3 18) "s", Located (Loc 0 4 10) "f", Located (Loc 0 4 12) "s"]
    , testProperty "the name at a location is the text there" $
        forAll genCode $ \code ->
          let ls = T.splitOn "\n" code
              at (Located (Loc _ l c) n) = T.take (T.length n) (T.drop (c - 1) (ls !! (l - 1)))
           in conjoin [counterexample (show v) (at v === unLoc v) | v <- codeVariables (Loc 0 1 1) code]
    ]

names :: Text -> [Text]
names = map unLoc . codeVariables (Loc 0 1 1)

-- Code and the variables it refers to.
reads' :: [(Text, [Text])]
reads' =
  [ ("x + y", ["x", "y"])
  , ("length \"y\" + x", ["length", "x"])
  , ("\"a\\\"y\\\" \" ++ x", ["x"])
  , ("\"\\\\\" ++ y", ["y"])
  , ("'y' : x", ["x"])
  , ("'\\'' : x", ["x"])
  , ("'\\n' : '\\x41' : x", ["x"])
  , ("x -- y", ["x"])
  , ("x -- y\n  + z", ["x", "z"])
  , ("x --> y", ["x", "y"])
  , ("x --| y", ["x", "y"])
  , ("x {- y -} z", ["x", "z"])
  , ("x {- {- y -} -} z", ["x", "z"])
  , ("x {- y\n z -} w", ["x", "w"])
  , ("M.y x", ["x"])
  , ("Data.Map.lookup k m", ["k", "m"])
  , ("r.y", ["r"])
  , ("r.y.z + x", ["r", "x"])
  , ("x `div` y", ["x", "div", "y"])
  , ("x `M.div` y", ["x", "y"])
  , ("y'", ["y'"])
  , ("ys", ["ys"])
  , ("Just y", ["y"])
  , ("y0 1e10 0x1F", ["y0"])
  , ("let x = 1 in x", ["x", "x"])
  , ("\\x -> x", ["x", "x"])
  , ("case x of { _ -> y }", ["x", "y"])
  , ("_env _col", ["_env", "_col"])
  , ("値 + 次の値", ["値", "次の値"])
  , ("f (x) [y]", ["f", "x", "y"])
  , ("", [])
  ]

-- Pieces of Haskell-like code: names, literals, comments, operators,
-- qualified names, field selections and spaces, in a random order.
genCode :: Gen Text
genCode = T.concat <$> listOf piece
  where
    piece =
      frequency
        [ (6, elements ["x", "y'", "ys", "f", "_env", "値", "M.x", "Data.Map.lookup", "r.x", "Just", "div"])
        , (4, elements [" ", "  ", "\n", "\n  "])
        , (3, elements ["+", "-", "->", "`", "(", ")", "[", "]", ".", ",", "\\", "=", "$"])
        , (2, elements ["\"\"", "\"y\"", "\"a\\\"y\"", "\"\\\\\"", "'y'", "'\\''", "'\\n'", "'"])
        , (2, elements ["-- y", "--> y", "{- y -}", "{- {- y -} -}", "{- y\n -}"])
        , (1, elements ["1", "0x1F", "1e10", "1.5"])
        ]
