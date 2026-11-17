{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The probe of RenderPrinting.lean. It reads every grammar of the
-- repository, keeps those that parse, resolve their imports, expand their
-- templates and pass 'check', and builds the generator's 'Env' for each as
-- 'render' does. For every expression and subexpression of the rules, with
-- its value used and discarded, it runs exprCodeU of CodegenInternal (the
-- source of Peg.Codegen under another module name) and, beside it, builds
-- the printing tree of RenderPrinting.lean in the same order of fresh names.
-- Expressions that hold user code (a rule call with arguments, a predicate,
-- a label) and groups around them are skipped, and so are trees with rule
-- names outside ASCII, which the model's lexer does not read; exprCodeU still runs on them
-- so that the fresh names of their siblings stay those of the generator.
--
-- It writes three files into the directory given:
--
-- * RenderPrintingProbeCases.lean: the trees as a Lean module.
-- * haskell-text: the text of exprCodeU for each tree, one escaped line
--   each, in the format of RenderPrintingProbe.lean.
-- * P.hs: a Haskell module with one declaration @x = TEXT@ per tree, for
--   GHC's lexer.
--
-- It fails unless each printed text, with the fresh names masked, occurs in
-- the module that 'generate' returns for its grammar, after finalize, with
-- the value used or discarded, for every grammar without @%syntax@.
module Main (main) where

import CodegenInternal
import Control.Monad (forM, unless)
import Data.Char (isDigit, ord)
import Data.List (intercalate, sort)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Numeric (showHex)
import Peg.Grammar
import Peg.Grammar.Check (Analysis, check)
import Peg.Grammar.Import (resolveImports)
import Peg.Grammar.Import.Files (readImports)
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import Peg.Grammar.Types (hasValue)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (getArgs)
import System.Exit (die)
import System.FilePath (takeExtension, (</>))
import System.IO (hSetEncoding, stdout, utf8)

-- The printing tree, as Lean terms.
data P
  = PAny
  | PRef Text
  | PLit Text Text
  | PCls [(Char, Char)] Text
  | PWrap String P
  | PGroup [Body]
  deriving (Eq)

data Body = Body [Stmt] Final
  deriving (Eq)

data Stmt = SExpr P | SBind Text P | SDiscard P
  deriving (Eq)

data Final = FUnit | FVar Text
  deriving (Eq)

-- exprCodeU's choices, building the tree. Nothing for what the tree does not
-- cover; then exprCodeU itself runs, for the fresh names it takes.
toP :: Env -> Bool -> Expr -> Gen (Maybe P)
toP env used expr = case expr of
  ELit t o -> pure (Just (PLit t o))
  EClass rs o -> pure (Just (PCls rs o))
  EAny -> pure (Just PAny)
  ERef _ n [] -> pure (Just (PRef n))
  EGroup alts
    | used && hasValue (units env) expr -> do
        bodies <- mapM (passP env) alts
        pure (PGroup <$> sequence bodies)
    | otherwise -> do
        bodies <- mapM (\is -> mapM (stmtP env) is >>= \ss -> pure (flip Body FUnit <$> sequence ss)) alts
        pure (PGroup <$> sequence bodies)
  EStar x -> wrapP (if valued x then "many" else "skipMany") used x
  EPlus x -> wrapP (if valued x then "many1" else "skipMany1") used x
  EOpt x -> wrapP (if valued x then "optional" else "skipOptional") used x
  EAnd x -> wrapP "andP" False x
  ENot x -> wrapP "notP" False x
  ECapture x -> wrapP "capture" False x
  EDiscard x -> wrapP "voidP" False x
  _ -> Nothing <$ exprCodeU env used expr
  where
    valued x = used && hasValue (units env) x
    wrapP f inner x = fmap (PWrap f) <$> toP env inner x

-- passThrough env False.
passP :: Env -> [Item] -> Gen (Maybe Body)
passP env items = go items
  where
    chosen = passedItem env items
    go [] = pure (Just (Body [] FUnit))
    go (i : is)
      | Just i == chosen = do
          e <- toP env True (itemExpr i)
          v <- fresh
          rest <- mapM (stmtP env) is
          pure (Body <$> ((:) <$> (SBind v <$> e) <*> sequence rest) <*> pure (FVar v))
      | otherwise = do
          s <- stmtP env i
          rest <- go is
          pure (prepend <$> s <*> rest)
    prepend s (Body ss f) = Body (s : ss) f

-- itemStmt env False.
stmtP :: Env -> Item -> Gen (Maybe Stmt)
stmtP env i = do
  e <- toP env (valueUsed env False i) (itemExpr i)
  pure $
    if hasValue (units env) (itemExpr i)
      then SDiscard <$> e
      else SExpr <$> e

-- RenderPrinting.valid: the model's lexer reads ASCII identifiers only
-- (RenderExpressionLexer), so names with other letters are left out.
asciiNames :: P -> Bool
asciiNames = \case
  PRef n -> T.all idChar n
  PWrap _ x -> asciiNames x
  PGroup bs -> all body bs
  _ -> True
  where
    idChar c = c == '_' || c == '\'' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
    body (Body ss f) = all stmt ss && final f
    stmt = \case
      SExpr x -> asciiNames x
      SBind v x -> T.all idChar v && asciiNames x
      SDiscard x -> asciiNames x
    final = \case
      FUnit -> True
      FVar v -> T.all idChar v

subexpressions :: Expr -> [Expr]
subexpressions e = e : case e of
  EGroup alts -> concatMap (subexpressions . itemExpr) (concat alts)
  EStar x -> subexpressions x
  EPlus x -> subexpressions x
  EOpt x -> subexpressions x
  EAnd x -> subexpressions x
  ENot x -> subexpressions x
  ECapture x -> subexpressions x
  ELabel _ x _ -> subexpressions x
  EDiscard x -> subexpressions x
  _ -> []

hpegFiles :: FilePath -> IO [FilePath]
hpegFiles dir = do
  names <- sort <$> listDirectory dir
  concat
    <$> mapM
      ( \n -> do
          let p = dir </> n
          isDir <- doesDirectoryExist p
          if isDir && n `notElem` ["dist-newstyle", ".git", "node_modules"]
            then hpegFiles p
            else pure [p | takeExtension n == ".hpeg"]
      )
      names

prepare :: FilePath -> Text -> IO (Maybe (Grammar, Analysis))
prepare file src = case parseGrammar src of
  Left _ -> pure Nothing
  Right g0 -> do
    libs <- readImports file g0
    pure $ case libs >>= resolveImports g0 >>= expandTemplates >>= (\g -> (,) g <$> check g) of
      Left _ -> Nothing
      Right ga -> Just ga

-- The fresh names peg'vN, with N masked.
mask :: Text -> Text
mask t = case T.breakOn "peg'v" t of
  (before, rest)
    | T.null rest -> before
    | otherwise -> before <> "peg'v#" <> mask (T.dropWhile isDigit (T.drop 5 rest))

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  files <- concat <$> mapM hpegFiles ["packages", "conformance", "examples", "editors"]
  prepared <- forM files $ \f -> TIO.readFile f >>= fmap ((,) f) . prepare f
  let grammars = [(f, g, an) | (f, Just (g, an)) <- prepared]
  perGrammar <- forM grammars $ \(f, g, an) -> do
    let env = Env defaultOptions g an (M.fromList [(ruleName r, r) | r <- grammarRules g]) (isJust (grammarSyntax g)) ""
        subs = [x | r <- grammarRules g, a <- ruleAlts r, i <- altItems a, x <- subexpressions (itemExpr i)]
        printed x used = case fst (runGen (toP env used x) 0) of
          Just p -> Just (p, fst (runGen (exprCodeU env used x) 0))
          Nothing -> Nothing
        found = [(x, [(p, txt) | used <- [True, False], Just (p, txt) <- [printed x used]]) | x <- subs]
    unless (isJust (grammarSyntax g)) $ case generate defaultOptions g of
      Left _ -> die ("generate failed: " ++ f)
      Right m -> do
        let masked = mask m
            missing = [x | (x, ps@(_ : _)) <- found, not (any (\(_, txt) -> mask txt `T.isInfixOf` masked) ps)]
        unless (null missing) $ die ("printed text not in the generated module of " ++ f ++ ": " ++ show (take 1 missing))
    pure [pt | (_, ps) <- found, pt <- ps]
  let printedAll = nubPairs (concat perGrammar)
      cases = [c | c@(p, _) <- printedAll, asciiNames p]
      skipped = length printedAll - length cases
  case args of
    [dir] -> do
      writeFile (dir </> "RenderPrintingProbeCases.lean") (leanModule (map fst cases))
      writeFile (dir </> "haskell-text") (unlines [("text " ++) (esc txt) | (_, txt) <- cases])
      TIO.writeFile (dir </> "P.hs") (T.unlines ("module P where" : ["x = " <> txt | (_, txt) <- cases]))
      putStrLn (show (length grammars) ++ " grammars, " ++ show skipped ++ " texts with non-ASCII names left out")
    _ -> die "usage: RenderPrintingProbe OUTPUT-DIRECTORY"
  where
    nubPairs = M.elems . M.fromList . map (\(p, txt) -> (txt, (p, txt)))

-- One line per text: backslash and newline escaped.
esc :: Text -> String
esc = concatMap e . T.unpack
  where
    e '\\' = "\\\\"
    e '\n' = "\\n"
    e c = [c]

leanModule :: [P] -> String
leanModule ps =
  unlines $
    [ "import RenderPrinting"
    , "open PegHs.RenderPrinting"
    , ""
    ]
      ++ concat (zipWith def [0 :: Int ..] ps)
      ++ ["def cases : List PExpr :=", "  [" ++ intercalate ", " ["case" ++ show i | i <- [0 .. length ps - 1]] ++ "]"]
  where
    def i p = ["def case" ++ show i ++ " : PExpr :=", "  " ++ expr p, ""]
    expr = \case
      PAny -> ".any"
      PRef n -> "(.ref " ++ str n ++ ")"
      PLit t o -> "(.lit " ++ str t ++ " " ++ str o ++ ")"
      PCls rs o -> "(.cls [" ++ intercalate ", " ["(Char.ofNat " ++ show (ord a) ++ ", Char.ofNat " ++ show (ord b) ++ ")" | (a, b) <- rs] ++ "] " ++ str o ++ ")"
      PWrap f x -> "(.wrap ." ++ f ++ " " ++ expr x ++ ")"
      PGroup (b : bs) -> "(.group " ++ body b ++ " " ++ foldr (\x acc -> "(.cons " ++ body x ++ " " ++ acc ++ ")") ".nil" bs ++ ")"
      PGroup [] -> error "a group without alternatives"
    body (Body ss f) = foldr (\s acc -> "(.cons " ++ stmt s ++ " " ++ acc ++ ")") ("(.last " ++ final f ++ ")") ss
    stmt = \case
      SExpr x -> "(.expr " ++ expr x ++ ")"
      SBind v x -> "(.bind " ++ str v ++ " " ++ expr x ++ ")"
      SDiscard x -> "(.discard " ++ expr x ++ ")"
    final = \case
      FUnit -> ".unit"
      FVar v -> "(.var " ++ str v ++ ")"

-- A Lean string literal.
str :: Text -> String
str t = "\"" ++ concatMap e (T.unpack t) ++ "\""
  where
    e '\\' = "\\\\"
    e '"' = "\\\""
    e '\n' = "\\n"
    e '\t' = "\\t"
    e c
      | ord c < 32 || ord c == 127 = "\\x" ++ (if ord c < 16 then "0" else "") ++ showHex (ord c) ""
      | otherwise = [c]
