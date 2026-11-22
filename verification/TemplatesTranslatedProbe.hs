{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import Data.Char (ord)
import Data.List (intercalate)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics
import Numeric (showHex)
import Peg.Grammar
import Peg.Grammar.Parser (parseGrammar)
import Peg.Grammar.Templates (expandTemplates)
import qualified TemplateCases
import System.Exit (die)

-- Derive only serialization for the public algebraic data, leaving the
-- package's definitions and its actual parse/expand functions untouched.
deriving instance Generic Loc
deriving instance Generic (Located a)
deriving instance Generic Grammar
deriving instance Generic Rule
deriving instance Generic Param
deriving instance Generic TemplateParam
deriving instance Generic Alt
deriving instance Generic Item
deriving instance Generic Expr
deriving instance Generic Diagnostic

class ToLean a where
  toLean :: a -> String
  default toLean :: (Generic a, GData (Rep a)) => a -> String
  toLean = gData . from

class GData f where
  gData :: f p -> String
instance (Datatype d, GCons f) => GData (M1 D d f) where
  gData m@(M1 value) = gCons ("TemplatesTranslated." ++ datatypeName m) value
class GCons f where
  gCons :: String -> f p -> String
instance (GCons f, GCons g) => GCons (f :+: g) where
  gCons name (L1 value) = gCons name value
  gCons name (R1 value) = gCons name value
instance (Constructor c, GFields f) => GCons (M1 C c f) where
  gCons name m@(M1 value) = "(" ++ name ++ "." ++ conName m ++ concatMap (" " ++) (gFields value) ++ ")"
class GFields f where
  gFields :: f p -> [String]
instance GFields U1 where gFields _ = []
instance ToLean a => GFields (K1 i a) where gFields (K1 value) = [toLean value]
instance GFields f => GFields (M1 S s f) where gFields (M1 value) = gFields value
instance (GFields f, GFields g) => GFields (f :*: g) where
  gFields (left :*: right) = gFields left ++ gFields right

instance ToLean Loc
instance ToLean a => ToLean (Located a)
instance ToLean Grammar
instance ToLean Rule
instance ToLean Param
instance ToLean TemplateParam
instance ToLean Alt
instance ToLean Item
instance ToLean Expr
instance ToLean Diagnostic
instance ToLean Int where toLean n = "(" ++ show n ++ " : Int)"
instance ToLean Char where toLean c = "(HsChar.ofNat " ++ show (ord c) ++ ")"
instance ToLean Bool where toLean value = if value then "true" else "false"
instance ToLean Text where
  toLean text = "\"" ++ concatMap escape (T.unpack text) ++ "\""
    where
      escape '"' = "\\\""
      escape '\\' = "\\\\"
      escape c | ord c < 0x20 || ord c == 0x7f = "\\x" ++ pad (showHex (ord c) "")
               | otherwise = [c]
      pad hex = replicate (2 - length hex) '0' ++ hex
instance ToLean a => ToLean [a] where toLean values = "[" ++ intercalate ", " (map toLean values) ++ "]"
instance ToLean a => ToLean (Maybe a) where
  toLean Nothing = "Option.none"
  toLean (Just value) = "(Option.some " ++ toLean value ++ ")"
instance (ToLean a, ToLean b) => ToLean (a,b) where
  toLean (left,right) = "(" ++ toLean left ++ ", " ++ toLean right ++ ")"
instance (ToLean a, ToLean b) => ToLean (Either a b) where
  toLean (Left value) = "(Except.error " ++ toLean value ++ ")"
  toLean (Right value) = "(Except.ok " ++ toLean value ++ ")"

main :: IO ()
main = do
  shared <- TemplateCases.cases
  let inputs = shared ++ [("unicode", T.pack "%module M\nS <- Box<[空]> Box<'𐐨'>\nBox<x> :: ()\nBox<x> <- x\n")]
  if null inputs then die "no template cases" else pure ()
  putStrLn "import TemplatesTranslated"
  putStrLn "def sameResult : Except (List TemplatesTranslated.Diagnostic) TemplatesTranslated.Grammar → Except (List TemplatesTranslated.Diagnostic) TemplatesTranslated.Grammar → Bool"
  putStrLn "  | .ok left, .ok right => left == right"
  putStrLn "  | .error left, .error right => left == right"
  putStrLn "  | _, _ => false"
  parsed <- mapM (\(name,source) -> case parseGrammar source of
    Left errors -> die (name ++ ": parse failure: " ++ show errors)
    Right grammar -> pure (name,grammar,expandTemplates grammar)) inputs
  mapM_ (\(index,(_,grammar,expected)) -> do
    putStrLn ("def input" ++ show index ++ " : TemplatesTranslated.Grammar := " ++ toLean grammar)
    putStrLn ("def expected" ++ show index ++ " : Except (List TemplatesTranslated.Diagnostic) TemplatesTranslated.Grammar := " ++ toLean expected))
    (zip [0 :: Int ..] parsed)
  putStrLn "def main : IO Unit := do"
  mapM_ (\(index,(name,_,_)) -> do
    putStrLn ("  unless sameResult (TemplatesTranslated.expandTemplates 4096 input" ++ show index ++ ") expected" ++ show index ++ " do")
    putStrLn ("    throw (IO.userError \"root ADR 0097 I2: translated template result differs: " ++ name ++ "\")"))
    (zip [0 :: Int ..] parsed)
  putStrLn ("  IO.println \"root ADR 0097 I2: compared all grammar fields and diagnostics in " ++ show (length parsed) ++ " template cases.\"")
