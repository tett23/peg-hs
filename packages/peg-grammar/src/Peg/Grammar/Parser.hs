{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | A hand-written parser for the @.peg@ notation (ADR 0004).
module Peg.Grammar.Parser
  ( parseGrammar
  , parseGrammarSelfHosted
  ) where

import Control.Monad (unless, when)
import Data.Char (isHexDigit, isSpace)
import Data.Text (Text)
import qualified Data.Text as T
import Numeric (readHex)
import Peg.Grammar
import Peg.Grammar.Assemble
import qualified Peg.Grammar.SelfHosted as SelfHosted
import Peg.Runtime (Pos (..), ParseError (..), renderParseError)

-- Parser ---------------------------------------------------------------------

data St = St
  { stInput :: !Text
  , stLine :: !Int
  , stCol :: !Int
  }

data Err = Err !Loc !Text

newtype Parser a = Parser {runP :: St -> Either Err (a, St)}

instance Functor Parser where
  fmap f (Parser p) = Parser $ \s -> fmap (\(a, s') -> (f a, s')) (p s)

instance Applicative Parser where
  pure x = Parser $ \s -> Right (x, s)
  Parser pf <*> Parser px = Parser $ \s -> case pf s of
    Left e -> Left e
    Right (f, s') -> fmap (\(x, s'') -> (f x, s'')) (px s')

instance Monad Parser where
  Parser p >>= k = Parser $ \s -> case p s of
    Left e -> Left e
    Right (x, s') -> runP (k x) s'

-- | Try the left parser; on failure, try the right one from the same state.
-- If both fail, report the error that got farther.
(<|>) :: Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser $ \s -> case p s of
  Right r -> Right r
  Left e1@(Err l1 _) -> case q s of
    Right r -> Right r
    Left e2@(Err l2 _) -> Left (if l1 >= l2 then e1 else e2)

infixl 3 <|>

optionalP :: Parser a -> Parser (Maybe a)
optionalP p = (Just <$> p) <|> pure Nothing

-- | Repeat a parser. A failure at the position where the attempt started,
-- ignoring leading whitespace, ends the repetition; a failure after
-- consuming input is an error.
manyP :: Parser a -> Parser [a]
manyP (Parser p) = Parser $ \s0 ->
  let go s acc = case p s of
        Right (x, s') -> go s' (x : acc)
        Left e@(Err l _)
          | l > startOf s -> Left e
          | otherwise -> Right (reverse acc, s)
   in go s0 []
  where
    startOf s = case runP ws s of
      Right (_, s') -> Loc (stLine s') (stCol s')
      Left _ -> Loc (stLine s) (stCol s)

sepBy1 :: Parser a -> Parser () -> Parser [a]
sepBy1 p sep = (:) <$> p <*> manyP (sep >> p)

getLoc :: Parser Loc
getLoc = Parser $ \s -> Right (Loc (stLine s) (stCol s), s)

getInput :: Parser Text
getInput = Parser $ \s -> Right (stInput s, s)

failAt :: Loc -> Text -> Parser a
failAt l msg = Parser $ \_ -> Left (Err l msg)

failHere :: Text -> Parser a
failHere msg = getLoc >>= \l -> failAt l msg

peek :: Parser (Maybe Char)
peek = Parser $ \s -> Right (fst <$> T.uncons (stInput s), s)

peekText :: Int -> Parser Text
peekText n = Parser $ \s -> Right (T.take n (stInput s), s)

advance :: Parser Char
advance = Parser $ \s -> case T.uncons (stInput s) of
  Nothing -> Left (Err (Loc (stLine s) (stCol s)) "unexpected end of file")
  Just (c, rest)
    | c == '\n' -> Right (c, St rest (stLine s + 1) 1)
    | otherwise -> Right (c, St rest (stLine s) (stCol s + 1))

char :: Char -> Parser ()
char c =
  peek >>= \case
    Just c' | c == c' -> () <$ advance
    _ -> failHere ("expected " <> T.pack (show c))

string :: Text -> Parser ()
string t = do
  l <- getLoc
  next <- peekText (T.length t)
  if next == t then mapM_ (const advance) (T.unpack t) else failAt l ("expected " <> T.pack (show t))

eof :: Parser ()
eof = peek >>= maybe (pure ()) (const (failHere "expected a rule, a directive or %{ ... }%"))

-- | Run a parser without consuming input.
lookAhead :: Parser a -> Parser a
lookAhead (Parser p) = Parser $ \s -> fmap (\(a, _) -> (a, s)) (p s)

-- | Skip whitespace and comments.
ws :: Parser ()
ws =
  peek >>= \case
    Just c | isSpace c -> advance >> ws
    Just '#' -> skipLine >> ws
    _ -> pure ()
  where
    skipLine =
      peek >>= \case
        Just '\n' -> pure ()
        Nothing -> pure ()
        Just _ -> advance >> skipLine

inlineSpaces :: Parser ()
inlineSpaces =
  peek >>= \case
    Just c | c == ' ' || c == '\t' -> advance >> inlineSpaces
    _ -> pure ()

restOfLine :: Parser Text
restOfLine = T.pack <$> go
  where
    go =
      peek >>= \case
        Just '\n' -> pure []
        Nothing -> pure []
        Just _ -> (:) <$> advance <*> go

-- The text consumed by a parser.
sliceOf :: Parser a -> Parser (a, Text)
sliceOf p = do
  before <- getInput
  x <- p
  after <- getInput
  pure (x, T.take (T.length before - T.length after) before)

ident :: Parser Text
ident =
  peek >>= \case
    Just c | isIdentStart c -> T.pack <$> ((:) <$> advance <*> rest)
    _ -> failHere "expected an identifier"
  where
    rest =
      peek >>= \case
        Just c | isIdentChar c -> (:) <$> advance <*> rest
        _ -> pure []

-- | Parse a grammar file with the parser that peg-hs generates from its own
-- notation (grammar/Peg.peg). It returns the same grammar as 'parseGrammar'
-- for every valid file; the tests check this on all grammars in the
-- repository. Syntax errors are reported with the farthest position and the
-- expected terminals instead of the hand-written messages.
parseGrammarSelfHosted :: Text -> Either [Diagnostic] Grammar
parseGrammarSelfHosted src = case SelfHosted.parse src of
  Right tops -> assemble tops
  Left e ->
    let p = parseErrorPos e
        msg = T.drop 2 (T.dropWhile (/= ':') (T.drop 1 (T.dropWhile (/= ':') (renderParseError e))))
     in Left [Diagnostic (Loc (posLine p) (posColumn p)) msg]

-- Top level -------------------------------------------------------------------

-- | Parse a grammar file.
parseGrammar :: Text -> Either [Diagnostic] Grammar
parseGrammar src = case runP (ws >> manyP (topItem <* ws) <* eof) (St src 1 1) of
  Left (Err l m) -> Left [Diagnostic l m]
  Right (items, _) -> assemble items

topItem :: Parser Top
topItem = do
  l <- getLoc
  peek >>= \case
    Just '%' ->
      peekText 2 >>= \case
        "%{" -> string "%{" >> verbatim
        _ -> advance >> directive l
    Just c | isIdentStart c -> declaration l
    _ -> failAt l "expected a rule, a directive or %{ ... }%"

directive :: Loc -> Parser Top
directive l = do
  name <- ident
  inlineSpaces
  al <- getLoc
  TDirective l name al . directiveArg name <$> restOfLine

verbatim :: Parser Top
verbatim = do
  l <- getLoc
  body <- go
  string "}%"
  pure (uncurry TVerbatim (verbatimBody l body))
  where
    go =
      peekText 2 >>= \case
        "}%" -> pure ""
        "" -> failHere "unterminated %{ block"
        _ -> T.cons <$> advance <*> go

declaration :: Loc -> Parser Top
declaration l = do
  name <- ident
  params <-
    peek >>= \case
      Just '(' -> advance >> paramList
      _ -> pure []
  ws
  next <- peekText 2
  case next of
    "::" -> do
      string "::"
      inlineSpaces
      tl <- getLoc
      ty <- T.stripEnd <$> restOfLine
      when (T.null ty) (failAt tl "expected a type")
      pure (TAnnot l name params (Located tl ty))
    "<-" -> do
      unless (null params) (failAt l "parameters belong to the type annotation, not the definition")
      string "<-"
      TDef l name <$> sepBy1 alternative (ws >> char '/')
    _ -> failHere "expected :: or <-"

paramList :: Parser [Param]
paramList = do
  chunks <- argChunks
  mapM (\c -> either (failAt (locOf c)) pure (toParam c)) chunks

-- Comma separated Haskell fragments up to a closing parenthesis, which is
-- consumed. The opening parenthesis has already been consumed.
argChunks :: Parser [Located Text]
argChunks = do
  ws
  chunk <- hsChunk ",)"
  when (T.null (T.strip (unLoc chunk))) (failAt (locOf chunk) "expected an argument")
  advance >>= \case
    ',' -> (chunk :) <$> argChunks
    _ -> pure [chunk]

-- Expressions -----------------------------------------------------------------

alternative :: Parser Alt
alternative = do
  ws
  l <- getLoc
  items <- manyP item
  ws
  action <-
    peek >>= \case
      Just '{' -> advance >> Just <$> (hsChunk "}" <* char '}')
      _ -> pure Nothing
  pure (Alt l items action)

-- Fails, without consuming input, at the start of a declaration.
notDeclStart :: Parser ()
notDeclStart = do
  l <- getLoc
  isDecl <- lookAhead ((True <$ declHead) <|> pure False)
  when isDecl (failAt l "declaration")
  where
    declHead = do
      _ <- ident
      peek >>= \case
        Just '(' -> advance >> hsChunk ")" >> () <$ advance
        _ -> pure ()
      ws
      next <- peekText 2
      unless (next == "::" || next == "<-") (failHere "not a declaration")

item :: Parser Item
item = do
  ws
  notDeclStart
  l <- getLoc
  bind <- optionalP binding
  Item l bind <$> prefixExpr
  where
    binding = do
      n <- ident
      char ':'
      peek >>= \case
        Just ':' -> failHere "not a binding"
        _ -> pure n

prefixExpr :: Parser Expr
prefixExpr = do
  ws
  peek >>= \case
    Just '&' -> advance >> ws >> lookahead True EAnd
    Just '!' -> advance >> ws >> lookahead False ENot
    Just '$' -> advance >> ECapture <$> prefixExpr
    _ -> labeled
  where
    lookahead positive wrap =
      peek >>= \case
        Just '{' -> advance >> EPred positive <$> (hsChunk "}" <* char '}')
        _ -> wrap <$> prefixExpr

labeled :: Parser Expr
labeled = do
  e <- suffixExpr
  label <- optionalP $ do
    ws
    l <- getLoc
    char '^'
    (,) l <$> ident
  pure (maybe e (\(l, name) -> ELabel l e name) label)

suffixExpr :: Parser Expr
suffixExpr = primary >>= postfix
  where
    postfix e = do
      op <- optionalP $ do
        ws
        peek >>= \case
          Just c | c `elem` ("*+?" :: String) -> advance
          _ -> failHere "no postfix operator"
      case op of
        Just '*' -> postfix (EStar e)
        Just '+' -> postfix (EPlus e)
        Just '?' -> postfix (EOpt e)
        _ -> pure e

primary :: Parser Expr
primary = do
  ws
  l <- getLoc
  peek >>= \case
    Just '\'' -> literal '\''
    Just '"' -> literal '"'
    Just '[' -> charClass
    Just '.' -> EAny <$ advance
    Just '(' -> advance >> group
    Just c | isIdentStart c -> do
      name <- ident
      args <-
        peek >>= \case
          Just '(' -> advance >> argChunks
          _ -> pure []
      pure (ERef l name args)
    _ -> failAt l "expected an expression"

group :: Parser Expr
group = do
  alts <- sepBy1 (manyP item) (ws >> char '/')
  ws
  peek >>= \case
    Just '{' -> failHere "actions are not allowed inside a group"
    _ -> pure ()
  char ')'
  pure (EGroup alts)

literal :: Char -> Parser Expr
literal q = do
  (decoded, orig) <- sliceOf (advance >> go)
  pure (ELit (T.pack decoded) orig)
  where
    go =
      peek >>= \case
        Just c | c == q -> [] <$ advance
        Just '\\' -> (:) <$> escape <*> go
        Just '\n' -> failHere "unterminated literal"
        Nothing -> failHere "unterminated literal"
        Just _ -> (:) <$> advance <*> go

charClass :: Parser Expr
charClass = do
  (ranges, orig) <- sliceOf (advance >> items)
  pure (EClass ranges orig)
  where
    items = do
      first <- range
      rest <- go
      pure (first : rest)
    go =
      peek >>= \case
        Just ']' -> [] <$ advance
        _ -> (:) <$> range <*> go
    range = do
      l <- getLoc
      a <- classChar
      two <- peekText 2
      case T.unpack two of
        ['-', c] | c /= ']' -> do
          _ <- advance
          b <- classChar
          when (b < a) (failAt l "the range is empty")
          pure (a, b)
        _ -> pure (a, a)
    classChar =
      peek >>= \case
        Just '\\' -> escape
        Just ']' -> failHere "empty character class"
        Just '\n' -> failHere "unterminated character class"
        Nothing -> failHere "unterminated character class"
        Just _ -> advance

escape :: Parser Char
escape = do
  l <- getLoc
  _ <- advance
  c <- advance
  case c of
    'n' -> pure '\n'
    't' -> pure '\t'
    'r' -> pure '\r'
    'u' -> do
      char '{'
      digits <- T.pack <$> hexDigits
      char '}'
      case readHex (T.unpack digits) of
        [(n, "")] | n <= 0x10FFFF -> pure (toEnum n)
        _ -> failAt l "invalid \\u escape"
    _ | c `elem` ("\\'\"][-" :: String) -> pure c
    _ -> failAt l ("unknown escape \\" <> T.singleton c)
  where
    hexDigits =
      peek >>= \case
        Just d | isHexDigit d -> (:) <$> advance <*> hexDigits
        _ -> pure []

-- Haskell fragments -----------------------------------------------------------

-- | Read Haskell code up to (not including) one of the stop characters at
-- bracket depth zero. String and character literals are skipped, so that
-- brackets inside them are not counted.
hsChunk :: String -> Parser (Located Text)
hsChunk stops = do
  l <- getLoc
  (_, t) <- sliceOf (go (0 :: Int) ' ')
  pure (Located l t)
  where
    go depth prev =
      peek >>= \case
        Nothing -> failHere "unterminated Haskell code"
        Just c
          | depth == 0 && c `elem` stops -> pure ()
          | c `elem` ("([{" :: String) -> advance >> go (depth + 1) c
          | c `elem` (")]}" :: String) ->
              if depth == 0 then failHere "unbalanced bracket in Haskell code" else advance >> go (depth - 1) c
          | c == '"' -> advance >> stringBody >> go depth '"'
          | c == '\'' && not (isIdentChar prev) -> charLiteral >> go depth '\''
          | otherwise -> advance >> go depth c
    stringBody =
      peek >>= \case
        Just '"' -> () <$ advance
        Just '\\' -> advance >> advance >> stringBody
        Nothing -> failHere "unterminated string literal"
        Just _ -> advance >> stringBody
    charLiteral = do
      next <- peekText 3
      case T.unpack next of
        ['\'', '\\', _] -> advance >> advance >> advance >> untilQuote
        ['\'', _, '\''] -> advance >> advance >> () <$ advance
        _ -> () <$ advance
    untilQuote =
      peek >>= \case
        Just '\'' -> () <$ advance
        Nothing -> failHere "unterminated character literal"
        Just _ -> advance >> untilQuote

