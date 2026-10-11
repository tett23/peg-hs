{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- | The two views of an expression compared with the reference
-- implementation (ADR 0022): the S-expression its metamethods report, and
-- the value of the small language of the evaluation probe.
module Conformance.Lua.Eval
  ( sexpr
  , Value (..)
  , evaluate
  , renderValue
  ) where

import Conformance.Lua.Ast
import Data.Text (Text)
import qualified Data.Text as T

-- | The tree as the metamethods of @trace.lua@ print it. Parentheses do not
-- show, a field and an index both print as @idx@, and a method call passes
-- its object first.
sexpr :: Exp -> Text
sexpr e = case e of
  EName n -> n
  EParen x -> sexpr x
  EBin op l r -> list [op, sexpr l, sexpr r]
  EUn "-" x -> list ["neg", sexpr x]
  EUn "~" x -> list ["bnot", sexpr x]
  EUn "#" x -> list ["len", sexpr x]
  EUn op x -> list [op, sexpr x]
  EField o k -> list ["idx", sexpr o, k]
  EIndex o k -> list ["idx", sexpr o, sexpr k]
  ECall f as -> list ("call" : sexpr f : map sexpr as)
  EMethod o m as -> list ("call" : list ["idx", sexpr o, m] : sexpr o : map sexpr as)
  other -> T.pack (show other)
  where
    list xs = "(" <> T.unwords xs <> ")"

-- | Values of the evaluation probe.
data Value = VInt Integer | VBool Bool | VNil
  deriving (Eq, Show)

-- | Evaluate integers, booleans and nil under @+@, @-@, comparisons,
-- @and@, @or@ and @not@, as Lua does. 'Nothing' is a runtime error.
evaluate :: Exp -> Maybe Value
evaluate e = case e of
  ENum n -> Just (VInt (read (T.unpack n)))
  ETrue -> Just (VBool True)
  EFalse -> Just (VBool False)
  ENil -> Just VNil
  EParen x -> evaluate x
  EUn "-" x -> evaluate x >>= \case
    VInt i -> Just (VInt (negate i))
    _ -> Nothing
  EUn "not" x -> VBool . not . truthy <$> evaluate x
  EBin "and" l r -> evaluate l >>= \v -> if truthy v then evaluate r else Just v
  EBin "or" l r -> evaluate l >>= \v -> if truthy v then Just v else evaluate r
  EBin op l r -> do
    a <- evaluate l
    b <- evaluate r
    binary op a b
  _ -> Nothing
  where
    truthy v = v /= VNil && v /= VBool False
    binary op a b = case (op, a, b) of
      ("+", VInt x, VInt y) -> Just (VInt (x + y))
      ("-", VInt x, VInt y) -> Just (VInt (x - y))
      ("==", _, _) -> Just (VBool (a == b))
      ("~=", _, _) -> Just (VBool (a /= b))
      ("<", VInt x, VInt y) -> Just (VBool (x < y))
      (">", VInt x, VInt y) -> Just (VBool (x > y))
      ("<=", VInt x, VInt y) -> Just (VBool (x <= y))
      (">=", VInt x, VInt y) -> Just (VBool (x >= y))
      _ -> Nothing

-- | A value as Lua's @tostring@ prints it, or @error@.
renderValue :: Maybe Value -> Text
renderValue = \case
  Just (VInt i) -> T.pack (show i)
  Just (VBool True) -> "true"
  Just (VBool False) -> "false"
  Just VNil -> "nil"
  Nothing -> "error"
