{-# LANGUAGE LambdaCase #-}

-- | Indenting the output of 'show' along its brackets (ADR 0036). The
-- tokens are kept: only the spaces between them change. peg-hs parse
-- compiles this module, which depends only on base, with the parser it
-- generates.
module Pretty (pretty, readable) where

import Data.Char (chr, isDigit, isPrint, isSpace)

-- | The output of 'show' with the characters outside ASCII of its string
-- literals as themselves, such as @\"あ\"@ for @\"\\12354\"@, so that text in
-- any language can be read (ADR 0045). Characters that are not printable
-- keep their escapes.
readable :: String -> String
readable = outside
  where
    outside = \case
      [] -> []
      '"' : rest -> '"' : inside rest
      c : rest -> c : outside rest
    inside = \case
      [] -> []
      '"' : rest -> '"' : outside rest
      '\\' : rest@(d : _)
        | isDigit d ->
            let (digits, rest') = span isDigit rest
                n = read digits :: Int
             in if length digits <= 7 && n >= 128 && n <= 0x10FFFF && isPrint (chr n)
                  then chr n : inside (dropSeparator rest')
                  else '\\' : digits <> inside rest'
      '\\' : x : rest -> '\\' : x : inside rest
      c : rest -> c : inside rest
    -- \& ends a numeric escape before a digit; a character needs no end.
    dropSeparator = \case
      '\\' : '&' : rest -> rest
      rest -> rest

-- | The text laid out in lines of at most 80 characters where it can be:
-- a group that does not fit has its elements on lines of their own.
pretty :: String -> String
pretty = unlines . layout 0 . parseNodes . tokenize

data Token = Token Bool String
  -- ^ Whether spaces precede it, and its text.

data Node
  = Atom Bool String
  | Group Bool Char [Node] Char

width :: Int
width = 80

tokenize :: String -> [Token]
tokenize = go False
  where
    go _ [] = []
    go sp s@(c : rest)
      | isSpace c = go True rest
      | c == '"' = let (t, rest') = quoted '"' rest in Token sp (c : t) : go False rest'
      | c == '\'' = let (t, rest') = character rest in Token sp (c : t) : go False rest'
      | c `elem` "()[]{}," = Token sp [c] : go False rest
      | otherwise = let (t, rest') = break (\x -> isSpace x || x `elem` "()[]{},\"") s in Token sp t : go False rest'
    quoted q s = case s of
      '\\' : x : rest -> let (t, rest') = quoted q rest in ('\\' : x : t, rest')
      x : rest
        | x == q -> ([x], rest)
        | otherwise -> let (t, rest') = quoted q rest in (x : t, rest')
      [] -> ([], [])
    -- A character literal, or a quote that is part of a name.
    character s = case s of
      '\\' : _ -> quoted '\'' s
      x : '\'' : rest -> ([x, '\''], rest)
      _ -> let (t, rest) = break (\x -> isSpace x || x `elem` "()[]{},\"") s in (t, rest)

parseNodes :: [Token] -> [Node]
parseNodes ts = let (ns, _) = nodes ts in ns
  where
    nodes [] = ([], [])
    nodes (Token sp [o] : rest)
      | o `elem` "([{" =
          let (inner, rest') = nodes rest
           in case rest' of
                Token _ [c] : rest'' | c `elem` ")]}" -> let (more, after) = nodes rest'' in (Group sp o inner c : more, after)
                _ -> ([Group sp o inner ' '], rest')
    nodes ts'@(Token _ [c] : _) | c `elem` ")]}" = ([], ts')
    nodes (Token sp t : rest) = let (more, after) = nodes rest in (Atom sp t : more, after)

-- One line, with one space where there were spaces.
flat :: [Node] -> String
flat = concat . zipWith piece [0 :: Int ..]
  where
    piece i n = (if i > 0 && spaced n then " " else "") <> case n of
      Atom _ t -> t
      Group _ o inner c -> [o] <> flat inner <> [c | c /= ' ']
    spaced = \case
      Atom sp _ -> sp
      Group sp _ _ _ -> sp

-- The lines of a sequence at an indentation; the first line starts at the
-- indentation too.
layout :: Int -> [Node] -> [String]
layout ind ns
  | ind + length (flat ns) <= width = [replicate ind ' ' <> flat ns]
  | otherwise = case ns of
      [Group _ o inner c] -> group ind o inner c
      [n] -> [replicate ind ' ' <> flat [n]]
      n : rest -> layout ind [n] <> concatMap (layout (ind + 2) . pure) rest
      [] -> []

-- A group that does not fit: its elements, separated by commas, on lines of
-- their own, with the commas first.
group :: Int -> Char -> [Node] -> Char -> [String]
group ind o inner c =
  case splitCommas inner of
    [part] ->
      -- No commas: the opening bracket starts the first line of the contents.
      case layout (ind + 1) part of
        first : rest -> (replicate ind ' ' <> [o] <> drop (ind + 1) first) : rest <> [replicate ind ' ' <> [c] | c /= ' ']
        [] -> [replicate ind ' ' <> [o] <> [c | c /= ' ']]
    parts ->
      concat
        [ case layout (ind + 2) part of
            first : rest -> (replicate ind ' ' <> [if i == 0 then o else ','] <> " " <> drop (ind + 2) first) : rest
            [] -> [replicate ind ' ' <> [if i == 0 then o else ',']]
        | (i, part) <- zip [0 :: Int ..] parts
        ]
        <> [replicate ind ' ' <> [c] | c /= ' ']

splitCommas :: [Node] -> [[Node]]
splitCommas = go []
  where
    go acc [] = [reverse acc]
    go acc (Atom _ "," : rest) = reverse acc : go [] rest
    go acc (n : rest) = go (n : acc) rest
