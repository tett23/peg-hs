-- | The abstract syntax of Lua 5.5 (ADR 0022), and the lexical checks the
-- grammar delegates to Haskell.
module Conformance.Lua.Ast
  ( Block (..)
  , Stat (..)
  , FuncName (..)
  , FuncBody (..)
  , Field (..)
  , Exp (..)
  , isKeyword
  , validNumeral
  , hexValue
  ) where

import Data.Char (digitToInt, isDigit, isHexDigit)
import Data.Text (Text)
import qualified Data.Text as T

-- | Statements and an optional return statement.
data Block = Block [Stat] (Maybe [Exp])
  deriving (Eq, Show)

data Stat
  = SEmpty
  | SAssign [Exp] [Exp]
  | SCall Exp
  | SLabel Text
  | SBreak
  | SGoto Text
  | SDo Block
  | SWhile Exp Block
  | SRepeat Block Exp
  | SIf [(Exp, Block)] (Maybe Block)
  | SForNum Text Exp Exp (Maybe Exp) Block
  | SForIn [Text] [Exp] Block
  | SFunction FuncName FuncBody
  | SLocalFunction Text FuncBody
  | SGlobalFunction Text FuncBody
  | -- | The attribute before the names, the names with their attributes,
    -- and the initial values.
    SLocal (Maybe Text) [(Text, Maybe Text)] [Exp]
  | SGlobal (Maybe Text) [(Text, Maybe Text)] [Exp]
  | -- | @global *@, with its attribute.
    SGlobalAll (Maybe Text)
  deriving (Eq, Show)

-- | Names separated by dots, and the method name after a colon.
data FuncName = FuncName [Text] (Maybe Text)
  deriving (Eq, Show)

-- | Parameters, the vararg parameter (@Just Nothing@ for an anonymous
-- @...@), and the body.
data FuncBody = FuncBody [Text] (Maybe (Maybe Text)) Block
  deriving (Eq, Show)

data Field
  = FKey Exp Exp
  | FName Text Exp
  | FPos Exp
  deriving (Eq, Show)

-- | Numerals and strings keep their lexeme.
data Exp
  = ENil
  | ETrue
  | EFalse
  | ENum Text
  | EStr Text
  | EVararg
  | EFunction FuncBody
  | ETable [Field]
  | EBin Text Exp Exp
  | EUn Text Exp
  | EName Text
  | EIndex Exp Exp
  | EField Exp Text
  | ECall Exp [Exp]
  | EMethod Exp Text [Exp]
  | EParen Exp
  deriving (Eq, Show)

-- | The reserved words. @global@ is not one: the reference implementation
-- is built with @LUA_COMPAT_GLOBAL@, which makes it a word whose meaning
-- depends on the context.
isKeyword :: Text -> Bool
isKeyword w =
  w
    `elem` map
      T.pack
      [ "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "goto", "if", "in"
      , "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while"
      ]

-- | Whether a lexeme read by the numeral rule converts to a number, as
-- @luaO_str2num@ decides: a decimal or hexadecimal mantissa with at least
-- one digit, and an optional exponent with at least one decimal digit.
validNumeral :: Text -> Bool
validNumeral t = case T.unpack t of
  '0' : x : rest | x `elem` "xX" -> number isHexDigit "pP" rest
  s -> number isDigit "eE" s
  where
    number digit marks s =
      let (intPart, r1) = span digit s
          (fracPart, r2) = case r1 of
            '.' : r -> span digit r
            _ -> ("", r1)
          hasDot = take 1 r1 == "."
          mantissaOk = not (null intPart && null fracPart)
       in mantissaOk && exponentOk marks (if hasDot then r2 else r1)
    exponentOk _ [] = True
    exponentOk marks (m : r)
      | m `elem` marks = case r of
          s : ds | s `elem` "+-" -> digits ds
          ds -> digits ds
      | otherwise = False
    digits ds = not (null ds) && all isDigit ds

-- | The value of hexadecimal digits, without bound.
hexValue :: Text -> Integer
hexValue = T.foldl' (\n c -> n * 16 + toInteger (digitToInt c)) 0
