{-# LANGUAGE OverloadedStrings #-}

-- | Tests of the libraries that grammars import (ADR 0092).
module Imports (importTests) where

import Control.Exception (bracket_)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Peg.Grammar
import Peg.Grammar.Check (check)
import Peg.Grammar.Import
import Peg.Grammar.Import.Files (readImport, readImports)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import System.Directory
import System.FilePath ((</>))
import Test.Tasty
import Test.Tasty.HUnit

importTests :: TestTree
importTests =
  testGroup
    "libraries (ADR 0092)"
    [ notationTests
    , pathTests
    , libraryTests
    , resolutionTests
    , nameTests
    , reachTests
    , templateTests
    , directiveTests
    , renderTests
    , importErrorTests
    , aloneTests
    , fileTests
    ]

-- The errors of a grammar as parsed, as (file, line, column, message).
parseErrors :: Text -> [(Int, Int, Int, Text)]
parseErrors src = either (map flat) (const []) (parseGrammar src)

flat :: Diagnostic -> (Int, Int, Int, Text)
flat (Diagnostic (Loc f l c) m) = (f, l, c, m)

-- The grammar with the rules of its libraries, as parsed.
resolved :: Text -> [(FilePath, Text)] -> Either [Diagnostic] Grammar
resolved src libs = parseGrammar src >>= \g -> resolveImports g libs

-- The errors of a grammar with its libraries, checked as by peg-hs gen.
checkErrors :: Text -> [(FilePath, Text)] -> [(Int, Int, Int, Text)]
checkErrors src libs = either (map flat) (const []) $ do
  g0 <- resolved src libs
  either (Left . templateNotes g0) Right (expandTemplates g0 >>= check)

ident :: Text
ident = T.unlines ["%library", "", "Ident :: Text", "Ident <- $(IdentStart IdentChar*) Sp", "", "IdentStart <- [a-zA-Z_]", "", "IdentChar <- [a-zA-Z0-9_]", "", "Sp <- [ \\t]*"]

calc :: Text
calc = T.unlines ["%module Calc.Parser", "%import lex/Ident.hpeg", "", "Assign :: (Text, Text)", "Assign <- n:Ident '=' Sp v:Ident { (n, v) }"]

notationTests :: TestTree
notationTests =
  testGroup
    "the notation"
    [ testCase "%import is read into grammarImports, without its comment" $
        fmap grammarImports (parseGrammar (T.replace "lex/Ident.hpeg" "lex/Ident.hpeg   # the identifiers" calc))
          @?= Right [Located (Loc 0 2 1) "lex/Ident.hpeg"]
    , testCase "%library is read into grammarLibrary" $
        fmap grammarLibrary (parseGrammar ident) @?= Right (Just (Loc 0 1 1))
    , testCase "a grammar has no %library" $
        fmap grammarLibrary (parseGrammar calc) @?= Right Nothing
    ]

pathTests :: TestTree
pathTests =
  testGroup
    "the paths of %import"
    ( [ testCase ("rejects " <> show p) $
          parseErrors (T.replace "lex/Ident.hpeg" p calc) @?= [(0, 2, 9, pathError)]
      | p <- ["../x.hpeg", "/abs.hpeg", "a//b.hpeg", "./a.hpeg", "a.peg", "a b.hpeg", "a\tb.hpeg", "a\x01\&b.hpeg", "\228.hpeg", "lex/../x.hpeg", "lex/", ".hpeg/"]
      ]
        ++ [ testCase ("accepts " <> show p) $ parseErrors (T.replace "lex/Ident.hpeg" p calc) @?= []
           | p <- ["lex/Ident.hpeg", "a-b_c.d.hpeg"]
           ]
        ++ [ testCase "isImportPath" $
               map isImportPath ["lex/Ident.hpeg", "a-b_c.d.hpeg", "../x.hpeg", "x.hpeg/", ""] @?= [True, True, False, False, False]
           , testCase "%import needs an argument" $
               parseErrors (T.replace "%import lex/Ident.hpeg" "%import" calc) @?= [(0, 2, 1, "%import needs an argument")]
           ]
    )
  where
    pathError = "%import expects a path such as lex/Ident.hpeg: parts of ASCII letters, digits, _, - and . separated by /, other than . and .., ending in .hpeg"

libraryTests :: TestTree
libraryTests =
  testGroup
    "what a library has"
    ( [ testCase "%module and %library" $
          parseErrors ("%module M\n" <> ident) @?= [(0, 2, 1, "%library and %module cannot be in the same file")]
      , testCase "%library twice" $
          parseErrors (ident <> "%library\n") @?= [(0, 11, 1, "duplicate %library directive")]
      , testCase "%library takes no argument" $
          parseErrors (T.replace "%library" "%library Lex" ident) @?= [(0, 1, 1, "%library takes no argument")]
      , testCase "a verbatim block" $
          parseErrors (T.replace "%library\n" "%library\n%{\nimport Data.Text (Text)\n}%\n" ident)
            @?= [(0, 3, 1, "a library cannot have %{ ... }%; write it in the grammar that imports the library")]
      , testCase "a library without rules is not a grammar to generate" $
          fmap (const ()) (parseGrammar ident >>= expandTemplates >>= check) @?= Left [Diagnostic (Loc 0 1 1) "missing %module directive"]
      , testCase "a file with neither %module nor %library" $
          parseErrors (T.replace "%library\n" "" ident) @?= [(0, 1, 1, "missing %module directive")]
      ]
        ++ [ testCase ("%" <> T.unpack d) $
               parseErrors (T.replace "%library\n" ("%library\n%" <> d <> arg <> "\n") ident)
                 @?= [(0, 2, 1, "a library cannot have %" <> d <> "; write it in the grammar that imports the library")]
           | (d, arg) <-
               [ ("start", " Ident")
               , ("entry", " Ident")
               , ("export", " f")
               , ("env", " Int")
               , ("tabstop", " 4")
               , ("nomemo", " Sp")
               , ("language", " OverloadedStrings")
               , ("syntax", "")
               , ("token", " Ident")
               , ("trivia", " Sp")
               , ("inline", " Sp")
               , ("recover", " lab Ident")
               , ("safe", " lab")
               , ("deriving", " Eq")
               , ("expect", " Ident \"an identifier\"")
               , ("message", " lab \"a message\"")
               , ("import", " other.hpeg")
               ]
           ]
    )

resolutionTests :: TestTree
resolutionTests =
  testGroup
    "the rules of the libraries"
    [ testCase "the rules of the grammar come first, then those of the libraries in the order of %import" $ do
        let root = T.unlines ["%module M", "%import b.hpeg", "%import a.hpeg", "S <- B A"]
            a = "%library\nA <- 'a'\n"
            b = "%library\nB <- 'b'\n"
        fmap (map (\r -> (ruleName r, locFile (ruleLoc r), locLine (ruleLoc r))) . grammarRules) (resolved root [("a.hpeg", a), ("b.hpeg", b)])
          @?= Right [("S", 0, 4), ("B", 1, 2), ("A", 2, 2)]
    , testCase "the grammar keeps its imports" $
        fmap grammarImports (resolved calc [("lex/Ident.hpeg", ident)]) @?= Right [Located (Loc 0 2 1) "lex/Ident.hpeg"]
    , testCase "a grammar with a library checks" $
        checkErrors calc [("lex/Ident.hpeg", ident)] @?= []
    , testCase "the locations in a library have its number" $
        either (const []) (concatMap (map (locFile . altLoc) . ruleAlts) . grammarRules) (resolved calc [("lex/Ident.hpeg", ident)])
          @?= [0, 1, 1, 1, 1]
    ]

nameTests :: TestTree
nameTests =
  testGroup
    "the names"
    [ testCase "a rule of the grammar and of a library with the same name" $
        checkErrors (calc <> "Sp <- ' '*\n") [("lex/Ident.hpeg", ident)] @?= [(1, 10, 1, "duplicate definition of Sp")]
    , testCase "rules of two libraries with the same name" $ do
        let root = T.unlines ["%module M", "%import a.hpeg", "%import b.hpeg", "S <- X Y"]
        checkErrors root [("a.hpeg", "%library\nX <- 'x'\nSp <- ' '\n"), ("b.hpeg", "%library\n\nY <- 'y'\nSp <- ' '\n")]
          @?= [(2, 4, 1, "duplicate definition of Sp")]
    , testCase "a library cannot call a rule of the grammar" $ do
        let root = T.unlines ["%module M", "%import a.hpeg", "S <- A Ws", "Ws <- ' '*"]
        checkErrors root [("a.hpeg", "%library\nA <- 'a' Ws\n")] @?= [(1, 2, 10, "undefined rule Ws")]
    , testCase "a library cannot call a rule of another library" $ do
        let root = T.unlines ["%module M", "%import a.hpeg", "%import b.hpeg", "S <- A B"]
        checkErrors root [("a.hpeg", "%library\nA <- 'a' B\n"), ("b.hpeg", "%library\nB <- 'b'\n")] @?= [(1, 2, 10, "undefined rule B")]
    ]

reachTests :: TestTree
reachTests =
  testGroup
    "reachability"
    [ testCase "the rules of a library that the grammar does not reach are not an error, and are left out" $ do
        let lib = "%library\nA <- 'a'\nUnused <- 'u'\n"
            root = T.unlines ["%module M", "%import a.hpeg", "S <- A"]
        checkErrors root [("a.hpeg", lib)] @?= []
        fmap (map ruleName . grammarRules) (resolved root [("a.hpeg", lib)]) @?= Right ["S", "A"]
    , testCase "a rule of the grammar that is not reached is an error" $ do
        let root = T.unlines ["%module M", "%import a.hpeg", "S <- A", "T <- A"]
        checkErrors root [("a.hpeg", "%library\nA <- 'a'\n")] @?= [(0, 4, 1, "rule T is unreachable from the start, entry and recovery rules")]
    ]

templateTests :: TestTree
templateTests =
  testGroup
    "templates"
    [ testCase "a template of a library takes a rule of the grammar" $ do
        let lib = "%library\nList<p :: a> :: [a]\nList<p> <- x:p xs:(',' p)* { x : xs }\n"
            root = T.unlines ["%module M", "%import list.hpeg", "S :: [Int]", "S <- List<N>", "N :: Int", "N <- '1' { 1 }"]
        checkErrors root [("list.hpeg", lib)] @?= []
    , testCase "an error in the expansion is at the template of the library" $ do
        let lib = "%library\nMany<p> :: ()\nMany<p> <- p* { () }\n"
            root = T.unlines ["%module M", "%import many.hpeg", "S <- Many<E>", "E <- 'a'?"]
        map (\(f, l, _, _) -> (f, l)) (checkErrors root [("many.hpeg", lib)]) @?= [(1, 3)]
    ]

directiveTests :: TestTree
directiveTests =
  testGroup
    "the directives of the grammar name the rules of the libraries"
    [ testCase "%token, %recover and %entry" $ do
        let lib = "%library\nIdent <- [a-z]+\nSkip <- (!'\\n' .)*\nNum <- [0-9]+\n"
            root = T.unlines ["%module M", "%syntax", "%import lex.hpeg", "%token Ident", "%entry Num", "%recover lab Skip", "S <- Ident ('=' ^lab) Ident"]
        checkErrors root [("lex.hpeg", lib)] @?= []
    ]

renderTests :: TestTree
renderTests =
  testCase "renderDiagnostic names the file of the location" $ do
    let imports = [Located (Loc 0 2 1) "lex/Ident.hpeg"]
    renderDiagnostic "grammar/Calc.hpeg" imports (Diagnostic (Loc 0 3 5) "m") @?= "grammar/Calc.hpeg:3:5: error: m"
    renderDiagnostic "grammar/Calc.hpeg" imports (Diagnostic (Loc 1 3 5) "m") @?= "grammar/lex/Ident.hpeg:3:5: error: m"
    renderDiagnostic "Calc.hpeg" imports (Diagnostic (Loc 1 3 5) "m") @?= "lex/Ident.hpeg:3:5: error: m"
    importedPath "a/b/Calc.hpeg" "lex/Ident.hpeg" @?= "a/b/lex/Ident.hpeg"

importErrorTests :: TestTree
importErrorTests =
  testGroup
    "the errors of %import"
    [ testCase "a path imported twice" $
        parseErrors (T.replace "%import lex/Ident.hpeg" "%import lex/Ident.hpeg\n%import lex/Ident.hpeg" calc)
          @?= [(0, 3, 1, "lex/Ident.hpeg is imported twice")]
    , testCase "a file without %library" $
        checkErrors calc [("lex/Ident.hpeg", T.replace "%library" "%module Lex" ident)]
          @?= [(0, 2, 1, "lex/Ident.hpeg is not a library: it has no %library directive")]
    , testCase "a path without a text" $
        checkErrors calc [] @?= [(0, 2, 1, "cannot import lex/Ident.hpeg: no such file")]
    , testCase "a library given as the grammar" $
        fmap (const ()) (resolved ident []) @?= Left [Diagnostic (Loc 0 1 1) "missing %module directive"]
    , testCase "a syntax error in a library is in the library" $
        checkErrors calc [("lex/Ident.hpeg", ident <> "X <- (\n")] @?= [(1, 12, 1, "expected ')'")]
    ]

aloneTests :: TestTree
aloneTests =
  testGroup
    "a library on its own"
    [ testCase "no start rule, reachability or values" $
        fmap libraryErrors (parseGrammar "%library\nA :: Int\nA <- B B\nB :: Int\nB <- '1' { 1 }\nC <- 'c'\n") @?= Right []
    , testCase "an undefined rule and a duplicate definition" $
        either (map flat) (map flat . libraryErrors) (parseGrammar "%library\nA <- B\nC <- 'c'\nC <- 'd'\n")
          @?= [(0, 4, 1, "duplicate definition of C")]
    , testCase "an undefined rule" $
        fmap (map flat . libraryErrors) (parseGrammar "%library\nA <- B\n") @?= Right [(0, 2, 6, "undefined rule B")]
    , testCase "the values are checked in the grammar that imports the library" $ do
        let lib = "%library\nA :: Int\nA <- B B\nB :: Int\nB <- '1' { 1 }\n"
            root = T.unlines ["%module M", "%import a.hpeg", "S :: Int", "S <- A"]
        checkErrors root [("a.hpeg", lib)] @?= [(1, 3, 6, "an alternative without an action must have exactly one element with a value, but it has 2")]
    ]

-- The files are made under a temporary directory, as
-- docs/audits/reproduce-symlink.sh does.
fileTests :: TestTree
fileTests =
  testCase "reading the libraries: symbolic links and missing files" $ do
    tmp <- getTemporaryDirectory
    let root = tmp </> "peg-grammar-import-test"
    bracket_ (removePathForcibly root >> createDirectoryIfMissing True (root </> "grammar" </> "lex")) (removePathForcibly root) $ do
      createDirectoryIfMissing True (root </> "outside")
      TIO.writeFile (root </> "grammar" </> "lex" </> "Ident.hpeg") ident
      TIO.writeFile (root </> "outside" </> "Ident.hpeg") ident
      createFileLink (root </> "outside" </> "Ident.hpeg") (root </> "grammar" </> "Linked.hpeg")
      createDirectoryLink (root </> "outside") (root </> "grammar" </> "linked")
      let at p = Located (Loc 0 2 1) p
          dir = root </> "grammar"
      r1 <- readImport dir (at "lex/Ident.hpeg")
      r1 @?= Right ident
      r2 <- readImport dir (at "Linked.hpeg")
      r2 @?= Left (Diagnostic (Loc 0 2 1) "cannot import Linked.hpeg: it is a symbolic link")
      r3 <- readImport dir (at "linked/Ident.hpeg")
      r3 @?= Left (Diagnostic (Loc 0 2 1) "cannot import linked/Ident.hpeg: it is a symbolic link")
      r4 <- readImport dir (at "lex/Missing.hpeg")
      r4 @?= Left (Diagnostic (Loc 0 2 1) "cannot import lex/Missing.hpeg: no such file")
      Right g <- pure (parseGrammar calc)
      r5 <- readImports (dir </> "Calc.hpeg") g
      r5 @?= Right [("lex/Ident.hpeg", ident)]
