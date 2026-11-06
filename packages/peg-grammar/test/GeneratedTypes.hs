{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The types of the rules without type annotations and actions (ADR 0075):
-- their classification, the errors of constructor names and @%deriving@,
-- the notation and its formatting and highlighting.
module GeneratedTypes (generatedTypeTests) where

import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Format (formatGrammar, sameGrammar)
import Peg.Grammar.Highlight
import Peg.Grammar.Outline (recoveredText)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import Peg.Grammar.Types
import Test.Tasty
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit

generatedTypeTests :: TestTree
generatedTypeTests =
  testGroup
    "types of rules without type annotations and actions (ADR 0075)"
    [ classificationTests
    , fixpointTests
    , comparisonTests
    , errorTests
    , notationTests
    ]

-- The type of each rule of a grammar, as written by 'describe'.
typesOf :: Text -> Either String [(Text, Text)]
typesOf src = case parseGrammar src >>= expandTemplates of
  Left ds -> Left (show ds)
  Right g ->
    let c = classify g
     in Right [(ruleName r, maybe "?" describe (M.lookup (ruleName r) (classRules c))) | r <- grammarRules g]

describe :: RuleType -> Text
describe = \case
  Annotated t -> "annotated " <> t
  UnitType -> "()"
  Inferred t -> "inferred " <> typeText t
  Generated d -> "generated " <> dataTypeText d

-- The type of the first rule of a grammar made of the given lines.
typeOfFirst :: [Text] -> Either String Text
typeOfFirst ls = typesOf (T.unlines ("%module M" : ls)) >>= \ts -> maybe (Left "no rule") (Right . snd) (lookup' ts)
  where
    lookup' ts = case ts of
      t : _ -> Just t
      [] -> Nothing

-- The type of a rule of a grammar made of the given lines.
typeOfRule :: Text -> [Text] -> Either String Text
typeOfRule n ls = typesOf (T.unlines ("%module M" : ls)) >>= maybe (Left "no rule") Right . lookup n

classificationTests :: TestTree
classificationTests =
  testGroup
    "the classification"
    [ testCase "a rule with a type annotation has the type written" $
        typeOfFirst ["A :: Int", "A <- n:$'1' { 1 }"] @?= Right "annotated Int"
    , testCase "in a grammar with %syntax, a rule without a type annotation has type ()" $
        typeOfFirst ["%syntax", "A <- $'a' B", "B <- $'b'"] @?= Right "()"
    , testCase "a rule with an action has type ()" $
        typeOfFirst ["A <- 'a' { () } / $'b'"] @?= Right "()"
    , testCase "no value other than () makes a rule of type ()" $
        typeOfFirst ["A <- 'a' Sp / Sp*", "Sp <- ' '"] @?= Right "()"
    , testCase "one value of one type in every alternative is inferred" $
        typeOfFirst ["A <- $'a' Sp / Sp $'b'", "Sp <- ' '"] @?= Right "inferred Text"
    , testCase "values of two types are generated" $
        typeOfFirst ["A <- $'a' / B", "B :: Int", "B <- 'b' { 1 }"] @?= Right "generated data A = A1 Text | A2 Int\n  deriving (Eq, Show)"
    , testCase "two values are generated, with one constructor" $
        typeOfFirst ["A <- $'a' Sp $'b'", "Sp <- ' '"] @?= Right "generated data A = A Text Text\n  deriving (Eq, Show)"
    , testCase "no value in an alternative is a constructor without arguments" $
        typeOfFirst ["A <- $'a' / 'b'"] @?= Right "generated data A = A1 Text | A2\n  deriving (Eq, Show)"
    , testCase "a constructor name generates a type that could be inferred" $
        typeOfFirst ["A <- $'a' @Word / $'b'"] @?= Right "generated data A = Word Text | A2 Text\n  deriving (Eq, Show)"
    , testCase "one constructor with one argument is a newtype" $
        typeOfFirst ["A <- $'a' @Word"] @?= Right "generated newtype A = Word Text\n  deriving (Eq, Show)"
    , testCase "bindings do not matter, and () values are left out" $
        typeOfFirst ["A <- s:Sp x:$'a' Sp y:$'b'", "Sp <- ' '"] @?= Right "generated data A = A Text Text\n  deriving (Eq, Show)"
    , testCase "repetitions, options, labels and groups" $
        typeOfFirst ["A <- B* B? ($'c' ^l) ($'d' / $'e') / B+ $('f'*)", "B :: Int", "B <- 'b' { 1 }"]
          @?= Right "generated data A = A1 [Int] (Maybe Int) Text Text | A2 [Int] Text\n  deriving (Eq, Show)"
    -- The type of an instance has the type of the argument in parentheses.
    , testCase "a template call has the type of its instance" $
        typeOfFirst ["A <- L<B> / C", "L<p :: a> :: [a]", "L<p> <- x:p xs:p* { x : xs }", "B :: Int", "B <- 'b' { 1 }", "C :: [(Int)]", "C <- 'c' { [] }"]
          @?= Right "inferred [(Int)]"
    , testCase "an argument of a template with an inferred type" $
        typeOfRule "A" ["A <- L<B> / C", "L<p :: a> :: [a]", "L<p> <- x:p xs:p* { x : xs }", "B <- $'b'", "C :: [(PegRt.Text)]", "C <- 'c' { [] }"]
          @?= Right "inferred [(PegRt.Text)]"
    , testCase "the name of a type of a rule name without case" $
        typeOfFirst ["値 <- $'a' $'b'"] @?= Right "generated data Rule'値 = Rule'値 Text Text\n  deriving (Eq, Show)"
    , testCase "%deriving changes the classes" $
        typeOfFirst ["%deriving Eq, Ord, Show", "A <- $'a' $'b'"] @?= Right "generated data A = A Text Text\n  deriving (Eq, Ord, Show)"
    , testCase "%deriving without arguments derives nothing" $
        typeOfFirst ["%deriving", "A <- $'a' $'b'"] @?= Right "generated data A = A Text Text"
    , testCase "the type of a constructor" $ do
        g <- either (assertFailure . show) pure (parseGrammar "%module M\nE <- E '+' T @Add / T\nT :: Int\nT <- 'n' { 1 }\n")
        [constructorTypeText d c | d <- classDataTypes (classify g), c <- dataConstructors d] @?= ["Add :: E -> Int -> E", "E2 :: Int -> E"]
    , testCase "the grammar of ADR 0075" $
        typesOf adrGrammar
          @?= Right
            [ ("Expr", "generated data Expr = Expr1 Expr Atom | Expr2 Atom\n  deriving (Eq, Show)")
            , ("Sp", "()")
            , ("Num", "inferred Text")
            , ("Paren", "inferred Expr")
            , ("Atom", "generated data Atom = Atom1 Text | Atom2 Expr\n  deriving (Eq, Show)")
            ]
    ]

adrGrammar :: Text
adrGrammar =
  T.unlines
    [ "%module M"
    , "Expr <- Expr '+' Sp Atom"
    , "      / Atom"
    , "Sp <- ' '*"
    , "Num <- $[0-9]+ Sp"
    , "Paren <- '(' Sp Expr ')' Sp"
    , "Atom <- Num / Paren"
    ]

fixpointTests :: TestTree
fixpointTests =
  testGroup
    "the fixed points"
    [ testCase "a rule that calls itself, without values" $
        typeOfFirst ["A <- '(' A ')' / 'x'"] @?= Right "()"
    , testCase "a rule that calls itself, with a value" $
        typeOfFirst ["A <- '(' A ')' / Num", "Num <- $[0-9]+"] @?= Right "inferred Text"
    , testCase "rules that call each other" $
        typesOf (T.unlines ["%module M", "A <- B / 'x'", "B <- '[' A ']' / $[0-9]+"])
          @?= Right
            [ ("A", "generated data A = A1 B | A2\n  deriving (Eq, Show)")
            , ("B", "generated data B = B1 A | B2 Text\n  deriving (Eq, Show)")
            ]
    , testCase "a candidate that is generated later takes its callers along" $
        typesOf (T.unlines ["%module M", "A <- B / $'y'", "B <- C / $'x'", "C <- D", "D <- $'a' $'b'"])
          @?= Right
            [ ("A", "generated data A = A1 B | A2 Text\n  deriving (Eq, Show)")
            , ("B", "generated data B = B1 D | B2 Text\n  deriving (Eq, Show)")
            , ("C", "inferred D")
            , ("D", "generated data D = D Text Text\n  deriving (Eq, Show)")
            ]
    , testCase "rules that call each other infer one type" $
        typesOf (T.unlines ["%module M", "A <- '(' B / $'a'", "B <- A ')'"])
          @?= Right
            [ ("A", "inferred Text")
            , ("B", "inferred Text")
            ]
    ]

comparisonTests :: TestTree
comparisonTests =
  testGroup
    "the comparison of types"
    [ testCase "spaces do not matter" $
        typeOfFirst ["A <- B / C", "B :: [Int]", "B <- 'b' { [] }", "C :: [ Int ]", "C <- 'c' { [] }"] @?= Right "inferred [Int]"
    , testCase "an alias is another type" $
        typeOfFirst ["%{", "type Name = Text", "}%", "A <- B / C", "B :: Text", "B <- $'b'", "C :: Name", "C <- $'c'"]
          @?= Right "generated data A = A1 Text | A2 Name\n  deriving (Eq, Show)"
    , testCase "a capture and a rule annotated Text" $
        typeOfFirst ["A <- B / $'c'", "B :: Text", "B <- $'b'"] @?= Right "inferred Text"
    , testCase "a rule annotated with an alias of () keeps its value" $
        typeOfFirst ["%{", "type Unit = ()", "}%", "A <- B", "B :: Unit", "B <- 'b' { () }"] @?= Right "inferred Unit"
    ]

-- The errors of a grammar made of the given lines, as (line, column,
-- message).
errorsIn :: [Text] -> [(Int, Int, Text)]
errorsIn ls = case parseGrammar (T.unlines ("%module M" : ls)) >>= \g -> expandTemplates g >>= check of
  Left ds -> [(locLine l, locColumn l, m) | Diagnostic l m <- ds]
  Right _ -> []

errorTests :: TestTree
errorTests =
  testGroup
    "errors"
    [ testCase "a constructor name in a rule with a type annotation" $
        errorsIn ["S :: Text", "S <- $'a' @A"] @?= [(3, 12, "@A names a constructor, but rule S has a type annotation")]
    , testCase "a constructor name in a grammar with %syntax" $
        errorsIn ["%syntax", "S <- $'a' @A"] @?= [(3, 12, "@A names a constructor, but the grammar has %syntax")]
    , testCase "a constructor name in a rule with an action" $
        errorsIn ["S <- 'a' { () }", "  / 'b' @B"] @?= [(3, 10, "@B names a constructor, but rule S has an action")]
    , testCase "a constructor name in a rule of type ()" $
        errorsIn ["S <- 'a' @A"] @?= [(2, 11, "@A names a constructor, but rule S has type (): no alternative has a value other than ()")]
    , testCase "a constructor name that does not start with an upper case letter" $
        errorsIn ["S <- $'a' @a"] @?= [(2, 12, "the constructor name a must start with an upper case letter")]
    , testCase "a constructor name given twice" $
        errorsIn ["S <- $'a' @A / $'b' @A"] @?= [(2, 22, "the constructor A is defined twice in rule S; name one of the alternatives with @Name")]
    , testCase "constructor names of two rules" $
        errorsIn ["S <- A / B", "A <- $'a' $'b' @X", "B <- $'c' $'d' @X"]
          @?= [(4, 17, "the constructor X of rule B is also a constructor of rule A; name one of the alternatives with @Name")]
    , testCase "a default name that is the name of the type of another rule" $
        errorsIn ["S <- S1 / $'b' $'c'", "S1 <- $'x' $'y' / 'z'"]
          @?= [(2, 6, "the constructor S1 of rule S has the name of the type of rule S1; name the alternative with @Name")]
    , testCase "a default name that is a constructor of another rule" $
        errorsIn ["S <- T / $'b' $'c'", "T <- $'x' $'y' @S1"]
          @?= [(3, 17, "the constructor S1 of rule T is also a constructor of rule S; name one of the alternatives with @Name")]
    , testCase "two rules with the same type name" $
        errorsIn ["S <- expr Expr", "expr <- $'a' $'b'", "Expr <- $'c' $'d'"]
          @?= [(4, 1, "the rules expr and Expr have the same type name Expr; rename one of them")]
    , testCase "%deriving twice" $
        errorsIn ["%deriving Eq", "%deriving Show", "S <- $'a' $'b'"] @?= [(3, 1, "duplicate %deriving directive")]
    , testCase "%deriving with a word that is not a class name" $
        errorsIn ["%deriving Eq, show", "S <- $'a' $'b'"] @?= [(2, 15, "%deriving expects class names, but got show")]
    , testCase "%deriving with a qualified class name" $
        errorsIn ["%deriving GHC.Generics.Generic", "S <- $'a' $'b'"] @?= []
    , testCase "two values without an action are no longer an error" $
        errorsIn ["S <- $'a' $'b'"] @?= []
    , testCase "an empty alternative of a generated rule is a constructor without arguments" $
        errorsIn ["S <- $'a' /"] @?= []
    , testCase "an empty alternative of a rule of type () is an error, as before" $
        map (\(_, _, m) -> m) (errorsIn ["S <- 'a' /"]) @?= ["an alternative without an action must have exactly one element with a value, but it has none"]
    ]

notationTests :: TestTree
notationTests =
  testGroup
    "the notation"
    [ testCase "the constructor names and %deriving are read" $ do
        g <- either (assertFailure . show) pure (parseGrammar notation)
        [fmap (\(Located l n) -> (locLine l, locColumn l, n)) (altConstructor a) | r <- grammarRules g, a <- ruleAlts r]
          @?= [Just (4, 20, "Add"), Nothing, Just (6, 17, "Lit"), Nothing, Nothing]
        fmap (\(Located l cs) -> (locLine l, map unLoc cs)) (grammarDeriving g) @?= Just (2, ["Eq", "Ord", "Show"])
    , testCase "the syntax tree has the text of the grammar" $
        recoveredText notation @?= notation
    , testCase "a constructor name needs a name after @" $
        either (map diagMessage) (const []) (parseGrammar "%module M\nS <- $'a' @\n") @?= ["expected a constructor name after @"]
    , testCase "a constructor name and an action" $
        either (map diagMessage) (const []) (parseGrammar "%module M\nS <- $'a' { () } @A\n") @?= []
    , goldenVsString "the formatting of constructor names and %deriving" "test/golden/format/constructors.hpeg" $ do
        src <- TIO.readFile "test/golden/format/constructors.txt"
        either (assertFailure . show) (pure . BL.fromStrict . TE.encodeUtf8) (formatGrammar src)
    , testCase "the formatting is idempotent and keeps the grammar" $ do
        src <- TIO.readFile "test/golden/format/constructors.txt"
        out <- either (assertFailure . show) pure (formatGrammar src)
        formatGrammar out @?= Right out
        assertBool "same grammar" (sameGrammar src out)
    , testCase "the highlights of constructor names and classes" $
        [(hlKind h, locLine (hlStart h), locColumn (hlStart h), locColumn (hlEnd h)) | h <- maybe [] id (highlights notation), hlKind h `elem` [HConstructor, HClassName]]
          @?= [(HClassName, 2, 11, 13), (HClassName, 2, 15, 18), (HClassName, 2, 20, 24), (HConstructor, 4, 20, 23), (HConstructor, 6, 17, 20)]
    ]

notation :: Text
notation =
  T.unlines
    [ "%module M"
    , "%deriving Eq, Ord, Show"
    , ""
    , "E <- E '+' Sp Num @Add"
    , "   / Num"
    , "   / '-' Num   @Lit # a comment"
    , "Num <- $[0-9]+"
    , "Sp <- ' '*"
    ]
