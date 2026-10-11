-- | Turn delimiter runs into emphasis, following the "process emphasis"
-- procedure of the CommonMark spec. This is a pure transformation of the
-- parsed inlines (ADR 0011 allows it after parsing); the characters around
-- each run are looked up from its byte offsets in the inline text.
module Conformance.CommonMark.Emphasis
  ( resolveEmphasis
  ) where

import Conformance.CommonMark.Types
import Data.Char (GeneralCategory (..), generalCategory)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Unsafe as TU

data D = D
  { dChar :: Char
  , dCount :: Int
  , dOrig :: Int
  , dOpen :: Bool
  , dClose :: Bool
  }

-- A delimiter that may open emphasis, with the inlines after it (reversed).
data Frame = Frame (Maybe D) [Inline]

-- | Resolve emphasis in a list of inlines and inside every link and image.
resolveEmphasis :: Text -> [Inline] -> [Inline]
resolveEmphasis src = go
  where
    go = process src . map inner
    inner (Link xs d t) = Link (go xs) d t
    inner (Image xs d t) = Image (go xs) d t
    inner x = x

process :: Text -> [Inline] -> [Inline]
process src = finish . foldl step [Frame Nothing []]
  where
    step frames tok = case tok of
      Delim c n s e -> handle (classify src c n s e) frames
      other -> add frames other

add :: [Frame] -> Inline -> [Frame]
add (Frame d xs : fs) x = Frame d (x : xs) : fs
add [] x = [Frame Nothing [x]]

literal :: D -> Inline
literal d = Str (T.replicate (dCount d) (T.singleton (dChar d)))

handle :: D -> [Frame] -> [Frame]
handle d frames
  | dClose d = case closeWith d frames of
      Just (frames', Nothing) -> frames'
      Just (frames', Just d') -> handle d' frames'
      Nothing
        | dOpen d -> Frame (Just d) [] : frames
        | otherwise -> add frames (literal d)
  | dOpen d = Frame (Just d) [] : frames
  | otherwise = add frames (literal d)

-- Find the nearest opener for a closer, wrap the inlines between them and
-- return the remaining closer, if any.
closeWith :: D -> [Frame] -> Maybe ([Frame], Maybe D)
closeWith d frames = search 0 frames
  where
    search _ [] = Nothing
    search k (f@(Frame (Just o) _) : rest)
      | matches o = Just (wrap (take k frames) f o rest)
      | otherwise = search (k + 1 :: Int) rest
    search k (_ : rest) = search (k + 1) rest
    matches o =
      dChar o == dChar d
        && dOpen o
        && not
          ( (dClose o || dOpen d)
              && (dOrig o + dOrig d) `mod` 3 == 0
              && not (dOrig o `mod` 3 == 0 && dOrig d `mod` 3 == 0)
          )
    wrap above (Frame _ content) o below =
      let inside = reverse content ++ concatMap flatten (reverse above)
          use = if dCount o >= 2 && dCount d >= 2 then 2 else 1
          node = if use == 2 then Strong inside else Emph inside
          o' = o {dCount = dCount o - use}
          d' = d {dCount = dCount d - use}
          frames'
            | dCount o' > 0 = Frame (Just o') [node] : below
            | otherwise = add below node
       in (frames', if dCount d' > 0 then Just d' else Nothing)

-- A frame as plain inlines, its delimiter becoming literal text.
flatten :: Frame -> [Inline]
flatten (Frame d xs) = maybe [] (pure . literal) d ++ reverse xs

finish :: [Frame] -> [Inline]
finish = concatMap flatten . reverse

-- Flanking rules ---------------------------------------------------------------

classify :: Text -> Char -> Int -> Int -> Int -> D
classify src c n s e = D c n n canOpen canClose
  where
    prev = fmap snd (T.unsnoc (TU.takeWord8 s src))
    next = fmap fst (T.uncons (TU.dropWord8 e src))
    left = not (isWs next) && (not (isPunct next) || isWs prev || isPunct prev)
    right = not (isWs prev) && (not (isPunct prev) || isWs next || isPunct next)
    (canOpen, canClose)
      | c == '*' = (left, right)
      | otherwise = (left && (not right || isPunct prev), right && (not left || isPunct next))

-- The start and end of the text count as whitespace.
isWs :: Maybe Char -> Bool
isWs Nothing = True
isWs (Just ch) = generalCategory ch == Space || ch `elem` ['\t', '\n', '\f', '\r']

-- Unicode punctuation: the P and S general categories.
isPunct :: Maybe Char -> Bool
isPunct Nothing = False
isPunct (Just ch) =
  generalCategory ch
    `elem` [ ConnectorPunctuation
           , DashPunctuation
           , OpenPunctuation
           , ClosePunctuation
           , InitialQuote
           , FinalQuote
           , OtherPunctuation
           , MathSymbol
           , CurrencySymbol
           , ModifierSymbol
           , OtherSymbol
           ]
