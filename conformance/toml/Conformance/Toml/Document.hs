{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Building a TOML document from the lines the grammar returns (ADR
-- 0023). The errors detected here are well formed by the grammar but not
-- by the whole document: duplicate keys, redefined tables, additions to
-- inline tables and static arrays, dates that do not exist, and integers
-- out of the 64-bit range. Building stops at the first error.
module Conformance.Toml.Document
  ( Value (..)
  , BuildError (..)
  , build
  ) where

import Conformance.Toml.Types
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Runtime (Span)

-- | A value of the document. Tables are maps; the order of keys is not
-- kept.
data Value
  = String Text
  | Integer Integer
  | Float Double
  | Bool Bool
  | DateTimeValue DateTime
  | Array [Value]
  | Table (Map Text Value)
  deriving (Show)

-- | An error, with the range of the line that caused it.
data BuildError = BuildError (Maybe Span) Text
  deriving (Eq, Show)

-- How a table came to exist, which decides what may extend it.
data Kind
  = -- | As a parent in a header, such as @a@ in @[a.b]@. A header may still
    -- define it once.
    Implicit
  | -- | By its own header.
    Explicit
  | -- | By a dotted key, such as @a@ in @a.b = 1@.
    Dotted
  | -- | By an inline table, closed to any addition.
    Inline
  deriving (Eq, Show)

data Node
  = NValue Value
  | NTable Kind (Map Text Node)
  | -- | An array of tables, from @[[ ]]@ headers, last one first.
    NArray [Map Text Node]

-- The state: the root table and the path of the current header. An array
-- of tables on the path stands for its last element.
data St = St (Map Text Node) Key

type Result a = Either BuildError a

-- | Build the document, or report the first error.
build :: [Line] -> Either BuildError (Map Text Value)
build ls = do
  St root _ <- foldl (\acc l -> acc >>= \st -> step st l) (Right (St M.empty [])) ls
  pure (M.map toValue root)

step :: St -> Line -> Result St
step st@(St root cur) = \case
  LBlank -> Right st
  LKeyVal sp k v -> do
    v' <- value sp v
    root' <- atPath sp cur root (\_ t -> insertDotted sp k v' t)
    Right (St root' cur)
  LTable sp k -> do
    root' <- header sp k root
    Right (St root' k)
  LArrayTable sp k -> do
    root' <- arrayHeader sp k root
    Right (St root' k)

failAt :: Span -> Text -> Result a
failAt sp msg = Left (BuildError (Just sp) msg)

-- Change the table at a path from the root that headers have opened.
atPath :: Span -> Key -> Map Text Node -> (Kind -> Map Text Node -> Result (Map Text Node)) -> Result (Map Text Node)
atPath _ [] t f = f Explicit t
atPath sp (p : ps) t f = case M.lookup p t of
  Just (NTable kind sub) -> do
    sub' <- if null ps then f kind sub else atPath sp ps sub f
    Right (M.insert p (NTable kind sub') t)
  Just (NArray (lastOne : rest)) -> do
    sub' <- atPath sp ps lastOne f
    Right (M.insert p (NArray (sub' : rest)) t)
  _ -> failAt sp ("no table at " <> p)

-- @[a.b.c]@: walk to the parent, creating implicit tables, then define the
-- last one.
header :: Span -> Key -> Map Text Node -> Result (Map Text Node)
header sp k root = walkParents sp k root $ \lastKey t -> case M.lookup lastKey t of
  Nothing -> Right (M.insert lastKey (NTable Explicit M.empty) t)
  Just (NTable Implicit sub) -> Right (M.insert lastKey (NTable Explicit sub) t)
  Just (NTable Explicit _) -> failAt sp ("table defined twice: " <> lastKey)
  Just (NTable Dotted _) -> failAt sp ("table defined by dotted keys: " <> lastKey)
  Just (NTable Inline _) -> failAt sp ("inline table: " <> lastKey)
  Just (NArray _) -> failAt sp ("array of tables: " <> lastKey)
  Just (NValue _) -> failAt sp ("key holds a value: " <> lastKey)

-- @[[a.b.c]]@: walk to the parent, then append a table.
arrayHeader :: Span -> Key -> Map Text Node -> Result (Map Text Node)
arrayHeader sp k root = walkParents sp k root $ \lastKey t -> case M.lookup lastKey t of
  Nothing -> Right (M.insert lastKey (NArray [M.empty]) t)
  Just (NArray ts) -> Right (M.insert lastKey (NArray (M.empty : ts)) t)
  Just (NValue (Array _)) -> failAt sp ("static array: " <> lastKey)
  Just _ -> failAt sp ("not an array of tables: " <> lastKey)

-- Walk the parents of a header's last key from the root. Headers may pass
-- through implicit, explicit and dotted tables, and through the last table
-- of an array of tables, but not into inline tables or values.
walkParents :: Span -> Key -> Map Text Node -> (Text -> Map Text Node -> Result (Map Text Node)) -> Result (Map Text Node)
walkParents sp k root f = go k root
  where
    go [] _ = failAt sp "empty key"
    go [lastKey] t = f lastKey t
    go (p : ps) t = case M.lookup p t of
      Nothing -> M.insert p . NTable Implicit <$> go ps M.empty <*> pure t
      Just (NTable Inline _) -> failAt sp ("inline table: " <> p)
      Just (NTable kind sub) -> (\sub' -> M.insert p (NTable kind sub') t) <$> go ps sub
      Just (NArray (lastOne : rest)) -> (\sub' -> M.insert p (NArray (sub' : rest)) t) <$> go ps lastOne
      Just _ -> failAt sp ("key holds a value: " <> p)

-- @a.b.c = v@ in a table: the parents are tables made by dotted keys, and
-- the last key must be new.
insertDotted :: Span -> Key -> Node -> Map Text Node -> Result (Map Text Node)
insertDotted sp k v = go k
  where
    go [] _ = failAt sp "empty key"
    go [lastKey] t
      | M.member lastKey t = failAt sp ("duplicate key: " <> lastKey)
      | otherwise = Right (M.insert lastKey v t)
    go (p : ps) t = case M.lookup p t of
      Nothing -> M.insert p . NTable Dotted <$> go ps M.empty <*> pure t
      Just (NTable Dotted sub) -> (\sub' -> M.insert p (NTable Dotted sub') t) <$> go ps sub
      Just _ -> failAt sp ("cannot extend with a dotted key: " <> p)

-- A value of a key, checked: inline tables become closed tables.
value :: Span -> Val -> Result Node
value sp = \case
  VInline kvs -> do
    t <- foldl (\acc (k, v) -> acc >>= \m -> value sp v >>= \v' -> insertDotted sp k v' m) (Right M.empty) kvs
    Right (NTable Inline t)
  v -> NValue <$> plain sp v

plain :: Span -> Val -> Result Value
plain sp = \case
  VString s -> Right (String s)
  VInteger i
    | i < -(2 ^ (63 :: Int)) || i > 2 ^ (63 :: Int) - 1 -> failAt sp ("integer out of range: " <> T.pack (show i))
    | otherwise -> Right (Integer i)
  VFloat d -> Right (Float d)
  VBool b -> Right (Bool b)
  VDateTime dt@(DateTime (Just (y, m, d)) _ _)
    | not (validDate y m d) -> failAt sp ("no such date: " <> T.pack (show (y, m, d)))
    | otherwise -> Right (DateTimeValue dt)
  VDateTime dt -> Right (DateTimeValue dt)
  VArray vs -> Array <$> mapM (\v -> value sp v >>= nodeValue) vs
  VInline kvs -> value sp (VInline kvs) >>= nodeValue
  VInvalid -> failAt sp "invalid value"
  where
    nodeValue n = Right (toValue n)

toValue :: Node -> Value
toValue = \case
  NValue v -> v
  NTable _ t -> Table (M.map toValue t)
  NArray ts -> Array (map (Table . M.map toValue) (reverse ts))
