{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the interpreter of grammars (ADR 0090).
module Interpret (interpretTests) where

import Data.Either (isRight)
import Data.Maybe (listToMaybe)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Labels (countGrammar, genGrammar, grammar, inputs, run, shadowGrammar)
import Peg.Grammar
import Peg.Grammar.Check
import Peg.Grammar.Interpret
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Peg.Runtime (ParseError (..), Pos (..), SyntaxError (..), renderParseError)
import Peg.Runtime.Syntax (SyntaxKind (..), debugTree, syntaxChildren, syntaxKind, syntaxText, syntaxTokens, tokenText)
import Shard (chunkedProperty)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

interpretTests :: TestTree
interpretTests =
  testGroup
    "the interpreter (ADR 0090)"
    ( [ leftRecursionTests
      , testCase "a label stops the ordered choice and is reported" $ do
          ip <- prepared (grammar ["S <- 'a' ('b' ^l) / 'a' 'c'"])
          fmap (const ()) (interpret ip Nothing "ab") @?= Right ()
          either (Just . parseErrorLabel) (const Nothing) (interpret ip Nothing "ac") @?= Just (Just "l")
          either (Just . parseErrorPos) (const Nothing) (interpret ip Nothing "ac") @?= Just (Pos 1 1 2)
      , testCase "the message of a label and the display name of a rule (ADR 0089)" $ do
          ip <- prepared (grammar ["%expect N \"a number\"", "%message close \"missing ')'\"", "S <- '(' N (')' ^close) / N", "N <- [0-9]+"])
          either (Just . renderParseError) (const Nothing) (interpret ip Nothing "x") @?= Just "1:1: expected a number or '('"
          either (Just . renderParseError) (const Nothing) (interpret ip Nothing "(1") @?= Just "1:3: missing ')'"
      , recoveryTests
      , testCase "integer arguments and predicates: exactly two spaces" $ do
          ip <- prepared countGrammar
          map (isRight . interpret ip Nothing) ["", " ", "  ", "   "] @?= [False, False, True, False]
      , testCase "_col follows %tabstop" $ do
          let src t = grammar (t ++ ["S <- ' '* '\\t'? &{ _col == 4 } 'x'"])
          tab4 <- prepared (src ["%tabstop 4"])
          plain <- prepared (src [])
          map (isRight . interpret tab4 Nothing) ["\tx", "    x", " \tx", "  x"] @?= [True, True, True, False]
          map (isRight . interpret plain Nothing) ["\tx", "    x", "   \tx"] @?= [False, True, True]
      , testCase "an argument with _col" $ do
          ip <- prepared (grammar ["S <- ' '* I(_col + 1)", "I(n :: Int) :: ()", "I <- &{ n == 3 } 'x'"])
          map (isRight . interpret ip Nothing) ["  x", " x"] @?= [True, False]
      , uninterpretableTests
      , testCase "arguments of parameters that only actions read are not evaluated" $ do
          assertBool "T.length" $ isRight $ prepare (grammar ["S :: Int", "S <- e:$'a'* x:A(T.length e) { x }", "A(n :: Text) :: Int", "A <- 'b' { n }"])
          assertBool "%env" $ isRight $
            prepare (T.replace "%module M\n" "%module M\n%env Int\n" (grammar ["S :: Int", "S <- 'a' { _env }"]))
      , testCase "the names of the kinds" $ do
          ip <- prepared (grammar ["%syntax", "%inline B", "S <- A B", "A <- 'a'", "B <- C", "C <- 'c'"])
          map (interpreterKindName ip . kindOf) [0, 1, 2, 3, 4, 5] @?= ["TEXT", "ERROR", "S", "A", "C", "UNKNOWN"]
      ]
        ++ chunkedProperty "it accepts what the interpreter of the label tests accepts" 2000 (\part ->
          forAll (variant part (T.replace " ^l)" ")" <$> genGrammar)) $ \src -> case parseGrammar src >>= \g -> (,) g <$> check g of
            Left _ -> discard
            Right (g, an)
              | not (S.null (analysisLeftRecursive an)) -> label "left recursion" True
              | otherwise -> case interpreter g an of
                  Left ds -> counterexample (show ds) False
                  Right ip ->
                    let agrees s = case run False g s of
                          Nothing -> True
                          Just ok -> ok == isRight (interpret ip Nothing (T.pack s))
                        bad = filter (not . agrees) inputs
                     in label "checked" (counterexample (T.unpack src <> "\ndiffers on " <> show (take 3 bad)) (null bad))
        )
    )
  where
    kindOf = SyntaxKind

leftRecursionTests :: TestTree
leftRecursionTests =
  testGroup
    "left recursion (ADR 0001)"
    [ testCase "E <- E '+' n / n is left associative" $ do
        ip <- prepared (grammar ["E <- E '+' 'n' / 'n'"])
        fmap (debugTree (interpreterKindName ip)) (interpret ip Nothing "n+n+n")
          @?= Right
            ( T.unlines
                [ "E@0..5"
                , "  E@0..3"
                , "    E@0..1"
                , "      TEXT@0..1 \"n\""
                , "    TEXT@1..3 \"+n\""
                , "  TEXT@3..5 \"+n\""
                ]
            )
    , testCase "indirect left recursion (Medeiros et al.)" $ do
        ip <- prepared (grammar ["L <- P '.x' / 'x'", "P <- P '(n)' / L"])
        fmap (map (interpreterKindName ip) . kinds) (interpret ip Nothing "x(n)(n).x(n).x")
          @?= Right ["L", "P", "P", "L", "P", "P", "P", "L"]
        isRight (interpret ip Nothing "x(n).x.") @?= False
    , testCase "left recursion behind a nullable prefix" $ do
        ip <- prepared (grammar ["E <- ' '* E '+' 'n' / 'n'"])
        fmap syntaxText (interpret ip Nothing "n+n+n") @?= Right "n+n+n"
        fmap (map (interpreterKindName ip) . kinds) (interpret ip Nothing "n+n+n") @?= Right ["E", "E", "E"]
    ]
  where
    -- The kinds of the nodes from the root down the first children.
    kinds n = syntaxKind n : maybe [] kinds (listToMaybe (syntaxChildren n))

recoveryTests :: TestTree
recoveryTests =
  testGroup
    "recovery (ADR 0021)"
    [ testCase "the tree has an error node and the error its range" $ do
        ip <- prepared recoverGrammar
        let (tree, errs) = interpretRecover ip Nothing "(a b;(b;"
        syntaxText tree @?= "(a b;(b;"
        map syntaxErrorRange errs @?= [(3, 5), (8, 8), (8, 8)]
        map syntaxErrorLabel errs @?= [Just "semi", Just "close", Just "close"]
        assertBool (T.unpack (debugTree (interpreterKindName ip) tree)) ("ERROR@" `T.isInfixOf` debugTree (interpreterKindName ip) tree)
    , testProperty "the tokens make the input" $
        forAll (T.pack <$> listOf (elements "(ab ;)")) $ \t ->
          case prepare recoverGrammar of
            Left ds -> counterexample (show ds) False
            Right ip -> T.concat (map tokenText (syntaxTokens (fst (interpretRecover ip Nothing t)))) === t
    ]
  where
    recoverGrammar =
      grammar
        [ "%recover semi SkipSemi"
        , "%recover close Skip"
        , "S <- Item*"
        , "Item <- '(' Word (';' ^semi) Item* (')' ^close) / Word ';'"
        , "Word <- [ab]+ ' '?"
        , "SkipSemi <- (!';' .)* ';'?"
        , "Skip <- (![()] .)*"
        ]

uninterpretableTests :: TestTree
uninterpretableTests =
  testGroup
    "grammars the interpreter cannot interpret"
    [ testCase "a predicate that calls a function" $
        messages (grammar ["S <- n:$[a-z]+ !{ isKeyword n }"]) @?= Left [(2, 18, "the interpreter cannot evaluate the predicate !{ isKeyword n }")]
    , testCase "a binding that hides a parameter" $
        messages shadowGrammar @?= Left [(5, 16, "the interpreter cannot evaluate the predicate &{ n == 1 }")]
    , testCase "a predicate that reads _env" $
        messages (T.replace "%module M\n" "%module M\n%env Int\n" (grammar ["S <- 'a' &{ _env > 0 }"])) @?= Left [(3, 12, "the interpreter cannot evaluate the predicate &{ _env > 0 }")]
    , testCase "an argument of a parameter read, that the interpreter cannot evaluate" $
        messages (grammar ["S <- e:$'a'* A(T.length e)", "A(n :: Int) :: ()", "A <- &{ n > 0 } 'b'"]) @?= Left [(2, 16, "the interpreter cannot evaluate the argument T.length e")]
    , testCase "a parameter read that is not of type Int" $
        messages (grammar ["S <- A(1)", "A(n :: Integer) :: ()", "A <- &{ n > 0 } 'b'"]) @?= Left [(3, 8, "the interpreter cannot read the parameter n, which is not of type Int")]
    , testCase "every predicate and argument is reported" $
        either length (const 0) (messages (grammar ["S <- &{ f 1 } A(g 2) &{ h }", "A(n :: Int) :: ()", "A <- &{ n > 0 } 'b'"])) @?= 3
    , testCase "a predicate inside a template names the call" $ do
        let src = grammar ["S <- T<'a'>", "T<p> :: ()", "T<p> <- p &{ f 1 }"]
            diags = do
              g0 <- parseGrammar src
              either (Left . templateNotes g0) Right (expandTemplates g0 >>= \g -> check g >>= interpreter g)
        case diags of
          Left ds -> ds @?= [Diagnostic (Loc 0 4 13) "the interpreter cannot evaluate the predicate &{ f 1 } (in the template T, expanded at 2:6)"]
          Right _ -> assertFailure "the interpreter accepted the grammar"
    ]
  where
    messages src = either (Left . map (\(Diagnostic (Loc _ l c) m) -> (l, c, m))) (const (Right ())) (prepare src)

-- Parse, expand, check and prepare a grammar, as peg-hs parse --interpret.
prepare :: Text -> Either [Diagnostic] Interpreter
prepare src = do
  g0 <- parseGrammar src
  g <- either (Left . templateNotes g0) Right (expandTemplates g0)
  an <- either (Left . templateNotes g0) Right (check g)
  either (Left . templateNotes g0) Right (interpreter g an)

prepared :: Text -> IO Interpreter
prepared src = either (\ds -> assertFailure (show ds) >> error "unreachable") pure (prepare src)
