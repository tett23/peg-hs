{-# LANGUAGE OverloadedStrings #-}

-- | The probe of FileTops.lean. It writes the edge cases below into the
-- directory given as the argument, lists them with every .hpeg file under
-- packages/ and editors/ in @manifest@ there, and prints what the real 'parseTops'
-- returns for each: the kind and the location of each 'Top', in order, or
-- @reject@. FileTopsProbe.lean prints the same from the item list of the
-- Lean model ('PegHs.FileTops.runTops'). Run it from the repository root.
-- The grammars of conformance/ are left out: the Lean model runs without
-- memoization, and some of them take minutes there.
module Main (main) where

import Control.Monad (forM, forM_, unless)
import Data.List (sort)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import qualified Data.Text.Encoding as TE
import Peg.Grammar (Loc (..))
import Peg.Grammar.Assemble (Top (..))
import Peg.Grammar.Parser (parseTops)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory, makeAbsolute)
import System.Environment (getArgs)
import System.Exit (die)
import System.FilePath (takeExtension, (</>))
import System.IO (hSetEncoding, stdout, utf8)

inline :: [(String, Text)]
inline =
  [ ("empty", "")
  , ("blank", "  \n\t\n")
  , ("comments", "# one\n  # two\n")
  , ("directive-eof", "%module M")
  , ("directive-comment", "# head\n%module M # tail\n")
  , ("directive-tab", "\t%module M\n\t%entry S\n")
  , ("verbatim-newline", "%{\nimport X\n}%\n%module M\n")
  , ("verbatim-inline", "%{ import X }%\n")
  , ("verbatim-spaces", "%{   import X\n}%")
  , ("verbatim-empty", "%{}%")
  , ("verbatim-adjacent", "%{\n}%%module M\n%{x}%%{y}%")
  , ("rules", "%module M\nS :: ()\nS <- 'a' { () }\n")
  , ("rules-no-annotation", "%module M\nS <- 'a' / 'b'\nT <- S S\n")
  , ("template", "%module M\nList<p> :: [()]\nList<p> <- p*\nS <- List<'a'>\n")
  , ("params", "%module M\nS(n :: Int) :: ()\nS <- 'a' { () }\n")
  , ("unicode", "%module M\n規則 :: ()\n規則 <- 'ア' { () }\n# 終わり\n")
  , ("crlf", "%module M\r\nS :: ()\r\nS <- 'a' { () }\r\n")
  , ("indented-rule", "%module M\n  S <- 'a'\n    / 'b'\n")
  , ("many", T.concat ["%language L" <> T.pack (show i) <> "\n" | i <- [1 :: Int .. 300]])
  , ("reject-trailing", "%module M\n@")
  , ("empty-rule", "S <-")
  , ("reject-verbatim", "%{ unterminated")
  , ("reject-ident", "Foo")
  , ("reject-directive", "% module")
  ]

repositoryGrammars :: IO [FilePath]
repositoryGrammars = concat <$> mapM walk ["packages", "editors"]
  where
    walk dir = do
      exists <- doesDirectoryExist dir
      if not exists
        then pure []
        else do
          names <- sort <$> listDirectory dir
          concat <$> forM names (\name -> do
            let path = dir </> name
            isDir <- doesDirectoryExist path
            isFile <- doesFileExist path
            pure' isDir isFile path)
    pure' isDir isFile path
      | isDir = walk path
      | isFile && takeExtension path == ".hpeg" = pure [path]
      | otherwise = pure []

loc :: Loc -> String
loc (Loc _ l c) = show l ++ ":" ++ show c

render :: Top -> String
render top = case top of
  TVerbatim l _ -> "verbatim " ++ loc l
  TDirective l _ _ _ -> "directive " ++ loc l
  TAnnot l _ _ _ _ -> "declaration " ++ loc l
  TDef l _ _ _ -> "declaration " ++ loc l

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  dir <- case args of
    [d] -> pure d
    _ -> die "usage: FileTopsProbe DIRECTORY"
  inlinePaths <- forM inline $ \(name, source) -> do
    let path = dir </> (name ++ ".hpeg")
    BS.writeFile path (TE.encodeUtf8 source)
    pure (name, path)
  grammars <- repositoryGrammars
  unless (length grammars >= 45) $ die "expected the .hpeg files of packages and editors"
  absolute <- mapM makeAbsolute grammars
  let cases = inlinePaths ++ zip grammars absolute
  writeFile (dir </> "manifest") (unlines [name ++ "\t" ++ path | (name, path) <- cases])
  forM_ cases $ \(name, path) -> do
    source <- TE.decodeUtf8 <$> BS.readFile path
    putStrLn ("case " ++ name)
    case parseTops source of
      Left _ -> putStrLn "reject"
      Right tops -> do
        putStrLn ("ok " ++ show (length tops))
        mapM_ (putStrLn . render) tops
