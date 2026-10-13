{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Templates together with parameterised rules (ADR 0055).
module TemplateParams (templateParamTests) where

import Data.List (sort)
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Highlight
import Peg.Grammar.Lint (LintWarning (..), lintGrammar)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Test.Tasty
import Test.Tasty.HUnit

templateParamTests :: TestTree
templateParamTests =
  testGroup
    "templates with parameterised rules (ADR 0055)"
    [ stage1Tests
    , stage2Tests
    , stage3Tests
    ]

-- Stage 1: the parameters of the caller that the arguments use.
stage1Tests :: TestTree
stage1Tests =
  testGroup
    "stage 1: the arguments take the parameters of the caller"
    [ testCase "an argument that uses a parameter makes an instance with it" $ do
        g <- expanded (base "B(ind :: Int) :: ()\nB <- Lines<Item(ind)> { () }")
        params g "Lines'0" @?= [("ind", "Int")]
        calls g "B" @?= [("Lines'0", ["ind"])]
    , testCase "a semantic predicate in the argument" $ do
        g <- expanded (base "B(ind :: Int) :: ()\nB <- Lines<(&{ ind > 0 } Item(0))> { () }")
        params g "Lines'0" @?= [("ind", "Int")]
        calls g "B" @?= [("Lines'0", ["ind"])]
    , testCase "only the parameters that the argument uses, in the order of their names" $ do
        g1 <- expanded (base "B(b :: Int, a :: Bool) :: ()\nB <- Lines<Item(b)> { () }")
        params g1 "Lines'0" @?= [("b", "Int")]
        g2 <- expanded (base "B(b :: Int, a :: Bool) :: ()\nB <- Lines<Pair(b, a)> { () }")
        params g2 "Lines'0" @?= [("a", "Bool"), ("b", "Int")]
        calls g2 "B" @?= [("Lines'0", ["a", "b"])]
    , testCase "qualified names, literals and reserved bindings are not taken" $ do
        g <- expanded (base "B(ind :: Int, env :: Int, col :: Int) :: ()\nB <- Lines<(Item(M.ind) Str(\"ind\") Chr('i') &{ _col > 0 && _env == () })> { () }")
        params g "Lines'0" @?= []
        calls g "B" @?= [("Lines'0", [])]
    , testCase "the same argument from two rules: one instance if the types agree, two otherwise" $ do
        g1 <- expanded (base "B(ind :: Int) :: ()\nB <- Lines<Item(ind)> C(ind) { () }\nC(ind :: Int) :: ()\nC <- Lines<Item(ind)> { () }")
        instances g1 @?= ["Lines'0"]
        g2 <- expanded (base "B(ind :: Int) :: ()\nB <- Lines<Item(ind)> C(1) { () }\nC(ind :: Integer) :: ()\nC <- Lines<Item(ind)> { () }")
        instances g2 @?= ["Lines'0", "Lines'1"]
        params g2 "Lines'1" @?= [("ind", "Integer")]
    , testCase "a template that calls a template passes the parameter on" $ do
        g <- expanded (base "B(ind :: Int) :: ()\nB <- Outer<Item(ind)> { () }\nOuter<p> :: ()\nOuter<p> <- Lines<p> { () }")
        params g "Outer'0" @?= [("ind", "Int")]
        params g "Lines'1" @?= [("ind", "Int")]
        calls g "Outer'0" @?= [("Lines'1", ["ind"])]
    , testCase "a template call in the argument takes the parameter too" $ do
        g <- expanded (base "B(ind :: Int) :: ()\nB <- Lines<Sep<Item(ind)>> { () }\nSep<p> :: ()\nSep<p> <- p ',' { () }")
        params g "Sep'0" @?= [("ind", "Int")]
        params g "Lines'1" @?= [("ind", "Int")]
        calls g "B" @?= [("Lines'1", ["ind"])]
    , testCase "a parameter that the instance does not use is named _x'" $ do
        g <- expanded (base "B(ind :: Int) :: ()\nB <- Skip<Item(ind)> { () }\nSkip<p> :: ()\nSkip<p> <- 'x' { () }")
        params g "Skip'0" @?= [("_ind'", "Int")]
        calls g "B" @?= [("Skip'0", ["ind"])]
    , testCase "a call that uses no parameter expands as before" $ do
        g <- expanded (base "B(ind :: Int) :: ()\nB <- Lines<Item(0)> { () }")
        params g "Lines'0" @?= []
        calls g "B" @?= [("Lines'0", [])]
    , testCase "an argument that uses a binding of the caller" $
        expansionErrors (base "B(ind :: Int) :: ()\nB <- x:N Lines<Item(x)> { () }")
          @?= [(13, 10, "the argument of the template Lines uses the binding x, which a template cannot take; pass it as a value argument")]
    , testCase "a binding to the right of the call is not in scope" $ do
        g <- expanded (base "B(x :: Int) :: ()\nB <- Lines<Item(x)> x:N { () }")
        params g "Lines'0" @?= [("x", "Int")]
    , testCase "a parameter with the name of a binding in the body of the template" $
        expansionErrors (base "B(x :: Int) :: ()\nB <- T<Item(x)> { () }\nT<p> :: ()\nT<p> <- x:N p { () }")
          @?= [(13, 6, "the template T uses the name x in its body, so its argument cannot take the parameter x of the rule B; rename the parameter")]
    , testCase "a parameter with the name of an identifier in the code of the template" $
        expansionErrors (base "B(x :: Int) :: ()\nB <- T<Item(x)> { () }\nT<p> :: ()\nT<p> <- p { let x = () in x }")
          @?= [(13, 6, "the template T uses the name x in its body, so its argument cannot take the parameter x of the rule B; rename the parameter")]
    , testCase "an instance with parameters in left recursion" $
        checkErrors (base "B(ind :: Int) :: ()\nB <- Rec<Item(ind)> { () }\nRec<p> :: ()\nRec<p> <- Rec<p> 'x' { () } / p { () }")
          @?= [(15, 1, "rule Rec'0 takes parameters and cannot take part in left recursion (in the template Rec, expanded at 13:6)")]
    , testCase "an instance without parameters can still take part in left recursion" $
        checkErrors (base "B(ind :: Int) :: ()\nB <- Rec<Item(0)> { () }\nRec<p> :: ()\nRec<p> <- Rec<p> 'x' { () } / p { () }") @?= []
    ]

-- Stage 2: the notation of a call with value arguments.
stage2Tests :: TestTree
stage2Tests =
  testGroup
    "stage 2: the notation of value arguments"
    [ testCase "a template call with value arguments" $ do
        g <- parsed (base "B(ind :: Int) :: ()\nB <- Lines<Item(ind)>(ind + 2, 3) { () }")
        exprsOf g "B" @?= [[ETemplate (Loc 13 6) "Lines" [ERef (Loc 13 12) "Item" [Located (Loc 13 17) "ind"]] [Located (Loc 13 23) "ind + 2", Located (Loc 13 32) "3"]]]
    , testCase "a space before the parenthesis makes a group" $ do
        g <- parsed (base "B(ind :: Int) :: ()\nB <- Lines<Item(ind)> (N) { () }")
        exprsOf g "B" @?= [[ETemplate (Loc 13 6) "Lines" [ERef (Loc 13 12) "Item" [Located (Loc 13 17) "ind"]] [], EGroup [[Item (Loc 13 24) Nothing (ERef (Loc 13 24) "N" [])]]]]
    , testCase "a template takes no value arguments" $
        expansionErrors (base "B(ind :: Int) :: ()\nB <- Lines<Item(ind)>(ind) { () }")
          @?= [(13, 6, "the template Lines takes no value arguments")]
    , testCase "a value argument in the template call of an argument" $
        expansionErrors (base "B(ind :: Int) :: ()\nB <- Lines<Lines<Item(ind)>(1)> { () }")
          @?= [(13, 12, "the template Lines takes no value arguments")]
    , testCase "the value arguments are highlighted as the arguments of a rule call" $ do
        let src = base "B(ind :: Int) :: ()\nB <- Lines<Item(ind)>(ind + 2) Item(ind) { () }"
            kindsAt l = [(locColumn (hlStart h), locColumn (hlEnd h), hlKind h) | h <- maybe [] id (highlights src), locLine (hlStart h) == l, hlKind h `elem` [HArguments, HRuleReference, HTemplateBracket]]
        kindsAt 13
          @?= [ (6, 11, HRuleReference)
              , (11, 12, HTemplateBracket)
              , (12, 16, HRuleReference)
              , (16, 21, HArguments)
              , (21, 22, HTemplateBracket)
              , (22, 31, HArguments)
              , (32, 36, HRuleReference)
              , (36, 41, HArguments)
              ]
    ]
  where
    parsed src = either (\ds -> assertFailure (show ds) >> error "unreachable") pure (parseGrammar src)
    exprsOf g n = [map itemExpr (altItems a) | r <- grammarRules g, ruleName r == n, a <- ruleAlts r]

-- Stage 3: the value parameters of templates.
stage3Tests :: TestTree
stage3Tests =
  testGroup
    "stage 3: value parameters of templates"
    [ testCase "an instance takes the value parameters, then the parameters of the caller" $ do
        g <- expanded (base3 "B(ind :: Int) :: ()\nB <- Indented<Item(ind)>(ind + 2) { () }")
        params g "Indented'0" @?= [("n", "Int"), ("ind", "Int")]
        calls g "B" @?= [("Indented'0", ["ind + 2", "ind"])]
    , testCase "the value parameters keep the order of their declaration" $ do
        g <- expanded (base3 "B(a :: Int) :: ()\nB <- Two<Item(a)>(1, True) { () }\nTwo<p>(z :: Int, y :: Bool) :: ()\nTwo<p> <- p &{ y && z > 0 } { () }")
        params g "Two'0" @?= [("z", "Int"), ("y", "Bool"), ("a", "Int")]
        calls g "B" @?= [("Two'0", ["1", "True", "a"])]
    , testCase "calls that differ only in the value arguments share an instance" $ do
        g <- expanded (base3 "B(ind :: Int) :: ()\nB <- Indented<Item(0)>(1) Indented<Item(0)>(ind) { () }")
        instances g @?= ["Indented'0"]
        calls g "B" @?= [("Indented'0", ["1"]), ("Indented'0", ["ind"])]
    , testCase "a value argument may use a binding to its left and _col" $ do
        checkErrors (base3 "B(ind :: Int) :: ()\nB <- x:N Indented<Item(ind)>(x + _col) { () }") @?= []
        g <- expanded (base3 "B(ind :: Int) :: ()\nB <- x:N Indented<Item(ind)>(x + _col) { () }")
        calls g "B" @?= [("Indented'0", ["x + _col", "ind"])]
    , testCase "a call in the body of a template takes its value parameters" $ do
        g <- expanded (base3 "B(ind :: Int) :: ()\nB <- Outer<Item(ind)>(2) { () }\nOuter<p>(m :: Int) :: ()\nOuter<p> <- Lines<Item(m)> p { () }")
        params g "Outer'0" @?= [("m", "Int"), ("ind", "Int")]
        calls g "Outer'0" @?= [("Lines'1", ["m"])]
    , testCase "the number of value arguments" $ do
        expansionErrors (base3 "B(ind :: Int) :: ()\nB <- Indented<Item(0)>(1, 2) { () }")
          @?= [(15, 6, "the template Indented expects 1 value argument(s), but got 2")]
        expansionErrors (base3 "B(ind :: Int) :: ()\nB <- Indented<Item(0)> { () }")
          @?= [(15, 6, "the template Indented expects 1 value argument(s), but got 0")]
    , testCase "value arguments for a template without value parameters" $
        expansionErrors (base3 "B(ind :: Int) :: ()\nB <- Lines<Item(0)>(1) { () }")
          @?= [(15, 6, "the template Lines takes no value arguments")]
    , testCase "value parameters in the definition of a template are an error, as for a rule" $ do
        let errorOf src = either (map diagMessage) (const []) (parseGrammar src)
        errorOf "%module M\nT<p>(n :: Int) :: ()\nT<p>(n :: Int) <- p { () }\n"
          @?= errorOf "%module M\nA(n :: Int) :: ()\nA(n :: Int) <- 'a' { () }\n"
        assertBool "an error" (not (null (errorOf "%module M\nT<p>(n :: Int) :: ()\nT<p>(n :: Int) <- p { () }\n")))
    , testCase "a value parameter with the name of a parameter of the caller" $
        expansionErrors (base3 "B(n :: Int) :: ()\nB <- Indented<Item(n)>(1) { () }")
          @?= [(15, 6, "the template Indented uses the name n in its body, so its argument cannot take the parameter n of the rule B; rename the parameter")]
    , testCase "an instance with value parameters in left recursion" $
        checkErrors (base3 "B(ind :: Int) :: ()\nB <- Rec<Item(0)>(1) { () }\nRec<p>(n :: Int) :: ()\nRec<p> <- Rec<p>(n) 'x' { () } / p { () }")
          @?= [(17, 1, "rule Rec'0 takes parameters and cannot take part in left recursion (in the template Rec, expanded at 15:6)")]
    , testCase "a binding used only in a value argument is used" $ do
        g <- either (\ds -> assertFailure (show ds) >> error "unreachable") pure (parseGrammar (base3 "B(ind :: Int) :: ()\nB <- x:N Indented<Item(ind)>(x) { () }"))
        [lintMessage w | w <- lintGrammar g] @?= []
    ]
  where
    base3 body = base ("Indented<p>(n :: Int) :: ()\nIndented<p> <- &{ n >= 0 } p { () }\n" <> body)

-- A grammar with templates and parameterised rules, with the body added
-- at line 12.
base :: Text -> Text
base body =
  T.unlines
    [ "%module M"
    , "S :: ()"
    , "S <- B(0) Pair(0, True) N { () }"
    , "Lines<p> :: ()"
    , "Lines<p> <- p ('\\n' p)* { () }"
    , "Item(n :: Int) :: ()"
    , "Item <- &{ n >= 0 } 'i' { () }"
    , "N :: Int"
    , "N <- [0-9] { 0 }"
    , "Pair(a :: Int, b :: Bool) :: ()"
    , "Pair <- 'p' { () }"
    , body
    ]

expanded :: Text -> IO Grammar
expanded src = case parseGrammar src >>= expandTemplates of
  Right g -> pure g
  Left ds -> assertFailure (show ds) >> error "unreachable"

-- The parameters of a rule, as (name, type).
params :: Grammar -> Text -> [(Text, Text)]
params g n = concat [[(paramName p, unLoc (paramType p)) | p <- ruleParams r] | r <- grammarRules g, ruleName r == n]

-- The calls of rules with arguments or of instances in a rule, as (name,
-- arguments).
calls :: Grammar -> Text -> [(Text, [Text])]
calls g n = [c | r <- grammarRules g, ruleName r == n, a <- ruleAlts r, i <- altItems a, c <- refs (itemExpr i), "'" `T.isInfixOf` fst c]
  where
    refs = \case
      ERef _ m args -> [(m, map unLoc args)]
      EGroup alts -> concatMap (concatMap (refs . itemExpr)) alts
      EStar x -> refs x
      EPlus x -> refs x
      EOpt x -> refs x
      EAnd x -> refs x
      ENot x -> refs x
      ECapture x -> refs x
      ELabel _ x _ -> refs x
      EDiscard x -> refs x
      _ -> []

instances :: Grammar -> [Text]
instances g = sort [ruleName r | r <- grammarRules g, "'" `T.isInfixOf` ruleName r]

-- The errors of expanding the templates, as (line, column, message).
expansionErrors :: Text -> [(Int, Int, Text)]
expansionErrors src = case parseGrammar src of
  Left ds -> [(0, 0, T.pack (show ds))]
  Right g0 -> case expandTemplates g0 of
    Left ds -> [(locLine l, locColumn l, m) | Diagnostic l m <- templateNotes g0 ds]
    Right _ -> []

-- The errors of expanding and checking, as (line, column, message).
checkErrors :: Text -> [(Int, Int, Text)]
checkErrors src = case parseGrammar src of
  Left ds -> [(0, 0, T.pack (show ds))]
  Right g0 -> case expandTemplates g0 >>= check of
    Left ds -> [(locLine l, locColumn l, m) | Diagnostic l m <- templateNotes g0 ds]
    Right _ -> []
