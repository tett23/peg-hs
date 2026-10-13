{-# LANGUAGE OverloadedStrings #-}

-- | Lossless syntax trees (ADR 0019), after rust-analyzer's rowan.
--
-- A t'GreenNode' is an immutable tree of kinds and text: every byte of the
-- input belongs to exactly one token, so the text of the tree is the input.
-- t'SyntaxNode' and t'SyntaxToken' wrap green elements with their absolute
-- offset and parent, and are what applications navigate.
--
-- Parsers generated from a grammar with @%syntax@ build these trees. For a
-- grammar with the rules @Expr@ and @Num@, the generated module exports:
--
-- * @parseSyntax :: Text -> Either ParseError SyntaxNode@, and with labels
--   (ADR 0021) @parseSyntaxRecover :: Text -> (SyntaxNode, [SyntaxError])@,
--   which always returns a tree;
-- * one constant per syntax kind, @syntaxKindExpr@ and @syntaxKindNum@, and
--   @nameOfSyntaxKind@ and @isTriviaSyntaxKind@;
-- * typed wrappers for the nodes of each rule, @newtype ExprSyntax@, with a
--   cast @castExprSyntax :: SyntaxNode -> Maybe ExprSyntax@ and one accessor
--   per binding, such as @exprLhs :: ExprSyntax -> Maybe ExprSyntax@ for a
--   binding @lhs:Expr@.
--
-- The children of a node are found with 'syntaxChildren' and
-- 'syntaxChildrenWithTokens', or by their labels (the binding names of the
-- grammar) with 'labeledNode' and the functions next to it:
--
-- @
-- case parseSyntax src of
--   Left err -> TIO.putStrLn (renderParseError err)
--   Right root -> do
--     TIO.putStr (debugTree nameOfSyntaxKind root)
--     print (syntaxText root == src)  -- always True
--     print [syntaxRange n | n <- syntaxChildren root, syntaxKind n == syntaxKindExpr]
-- @
module Peg.Runtime.Syntax
  ( -- * Kinds
    SyntaxKind (..)
  , textKind
  , errorKind
    -- * Green trees
  , GreenNode
  , GreenToken
  , GreenElement (..)
  , greenNodeKind
  , greenNodeChildren
  , greenTokenKind
  , greenTokenText
    -- * Syntax trees
  , SyntaxNode
  , SyntaxToken
  , SyntaxElement (..)
  , syntaxKind
  , syntaxLabel
  , syntaxRange
  , syntaxText
  , syntaxParent
  , syntaxChildren
  , syntaxChildrenWithTokens
  , syntaxTokens
  , syntaxPos
  , tokenKind
  , tokenLabel
  , tokenRange
  , tokenText
  , tokenParent
  , elementKind
  , elementLabel
    -- * Labelled children
  , labeledElements
  , labeledNode
  , labeledNodes
  , labeledToken
  , labeledTokens
    -- * Display
  , debugTree
    -- * Building (used by generated code)
  , Child (..)
  , setLabel
  , syntaxRoot
  ) where

import Data.Maybe (listToMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Unsafe as TU
import Peg.Runtime.Position (LineIndex, Pos, lineIndex, posIn)

-- | The kind of a node or token. Generated modules export one constant per
-- rule that is not @%inline@, named @syntaxKind@ followed by the rule name,
-- and @nameOfSyntaxKind@ to name a kind; 'textKind' (0) and 'errorKind' (1)
-- are fixed.
newtype SyntaxKind = SyntaxKind Int
  deriving (Eq, Ord, Show)

-- | Tokens of text matched by terminals outside @%token@ rules: the text
-- between the children of a node.
textKind :: SyntaxKind
textKind = SyntaxKind 0

-- | Error nodes: the ranges that error recovery skipped (ADR 0021). The
-- recovering entry points (@parseSyntaxRecover@) produce them.
errorKind :: SyntaxKind
errorKind = SyntaxKind 1

-- Green trees ------------------------------------------------------------------

-- | An immutable node: its kind, the length of its text in bytes, and its
-- children with their labels. It has no position, so it can be shared.
data GreenNode = GreenNode
  { gnKind :: !SyntaxKind
  , gnLength :: !Int
  , gnChildren :: [(Maybe Text, GreenElement)]
  }

-- | An immutable token: its kind and its text.
data GreenToken = GreenToken
  { gtKind :: !SyntaxKind
  , gtText :: !Text
  }

-- | A child of a green node.
data GreenElement = GreenNodeElement GreenNode | GreenTokenElement GreenToken

-- | The kind of a green node.
greenNodeKind :: GreenNode -> SyntaxKind
greenNodeKind = gnKind

-- | Children with their labels (the binding names of the grammar).
greenNodeChildren :: GreenNode -> [(Maybe Text, GreenElement)]
greenNodeChildren = gnChildren

-- | The kind of a green token.
greenTokenKind :: GreenToken -> SyntaxKind
greenTokenKind = gtKind

-- | The text of a green token.
greenTokenText :: GreenToken -> Text
greenTokenText = gtText

elementLength :: GreenElement -> Int
elementLength (GreenNodeElement n) = gnLength n
elementLength (GreenTokenElement t) = TU.lengthWord8 (gtText t)

-- Syntax trees -----------------------------------------------------------------

data Source = Source
  { srcText :: Text
  , srcLines :: LineIndex
  }

-- | A node with its absolute position and parent.
data SyntaxNode = SyntaxNode
  { snGreen :: GreenNode
  , snOffset :: !Int
  , snLabel :: Maybe Text
  , snParent :: Maybe SyntaxNode
  , snSource :: Source
  }

-- | A token with its absolute position and parent.
data SyntaxToken = SyntaxToken
  { stGreen :: GreenToken
  , stOffset :: !Int
  , stLabel :: Maybe Text
  , stParent :: SyntaxNode
  }

-- | A child of a node: a node or a token.
data SyntaxElement = NodeElement SyntaxNode | TokenElement SyntaxToken

instance Show SyntaxNode where
  show n = "SyntaxNode " <> show (syntaxKind n) <> " " <> show (syntaxRange n)

instance Show SyntaxToken where
  show t = "SyntaxToken " <> show (tokenKind t) <> " " <> show (tokenText t)

instance Show SyntaxElement where
  show (NodeElement n) = show n
  show (TokenElement t) = show t

instance Eq SyntaxNode where
  a == b = snOffset a == snOffset b && syntaxRange a == syntaxRange b && syntaxKind a == syntaxKind b

instance Eq SyntaxToken where
  a == b = stOffset a == stOffset b && tokenKind a == tokenKind b && tokenText a == tokenText b

instance Eq SyntaxElement where
  NodeElement a == NodeElement b = a == b
  TokenElement a == TokenElement b = a == b
  _ == _ = False

-- | The kind of a node.
syntaxKind :: SyntaxNode -> SyntaxKind
syntaxKind = gnKind . snGreen

-- | The label of the node in its parent, if a binding produced it.
syntaxLabel :: SyntaxNode -> Maybe Text
syntaxLabel = snLabel

-- | Byte offsets: start inclusive, end exclusive.
syntaxRange :: SyntaxNode -> (Int, Int)
syntaxRange n = (snOffset n, snOffset n + gnLength (snGreen n))

-- | The text of the node, made from its tokens.
syntaxText :: SyntaxNode -> Text
syntaxText = T.concat . map tokenText . syntaxTokens

-- | The parent of a node. The root has none.
syntaxParent :: SyntaxNode -> Maybe SyntaxNode
syntaxParent = snParent

-- | Child nodes, in order.
syntaxChildren :: SyntaxNode -> [SyntaxNode]
syntaxChildren n = [c | NodeElement c <- syntaxChildrenWithTokens n]

-- | Child nodes and tokens, in order.
syntaxChildrenWithTokens :: SyntaxNode -> [SyntaxElement]
syntaxChildrenWithTokens n = go (snOffset n) (gnChildren (snGreen n))
  where
    go _ [] = []
    go off ((label, e) : rest) =
      let el = case e of
            GreenNodeElement g -> NodeElement (SyntaxNode g off label (Just n) (snSource n))
            GreenTokenElement t -> TokenElement (SyntaxToken t off label n)
       in el : go (off + elementLength e) rest

-- | All tokens below the node, in order.
syntaxTokens :: SyntaxNode -> [SyntaxToken]
syntaxTokens root = go root []
  where
    -- An accumulator keeps this linear in the size of deep trees.
    go n acc = foldr step acc (syntaxChildrenWithTokens n)
    step (TokenElement t) acc = t : acc
    step (NodeElement c) acc = go c acc

-- | The line and column of a byte offset in the parsed input.
syntaxPos :: SyntaxNode -> Int -> Pos
syntaxPos n = posIn (srcText s) (srcLines s)
  where
    s = snSource n

-- | The kind of a token.
tokenKind :: SyntaxToken -> SyntaxKind
tokenKind = gtKind . stGreen

-- | The label of the token in its parent, if a binding produced it.
tokenLabel :: SyntaxToken -> Maybe Text
tokenLabel = stLabel

-- | Byte offsets: start inclusive, end exclusive.
tokenRange :: SyntaxToken -> (Int, Int)
tokenRange t = (stOffset t, stOffset t + TU.lengthWord8 (gtText (stGreen t)))

-- | The text of a token.
tokenText :: SyntaxToken -> Text
tokenText = gtText . stGreen

-- | The node that contains a token.
tokenParent :: SyntaxToken -> SyntaxNode
tokenParent = stParent

-- | The kind of a node or token.
elementKind :: SyntaxElement -> SyntaxKind
elementKind (NodeElement n) = syntaxKind n
elementKind (TokenElement t) = tokenKind t

-- | The label of a node or token in its parent.
elementLabel :: SyntaxElement -> Maybe Text
elementLabel (NodeElement n) = syntaxLabel n
elementLabel (TokenElement t) = tokenLabel t

-- Labelled children ------------------------------------------------------------

-- | Children with a label, skipping elements whose kind satisfies the
-- trivia predicate.
labeledElements :: (SyntaxKind -> Bool) -> Text -> SyntaxNode -> [SyntaxElement]
labeledElements isTrivia label n =
  [e | e <- syntaxChildrenWithTokens n, elementLabel e == Just label, not (isTrivia (elementKind e))]

-- | The first child node with a label and kind.
labeledNode :: SyntaxKind -> Text -> SyntaxNode -> Maybe SyntaxNode
labeledNode k label = listToMaybe . labeledNodes k label

-- | All child nodes with a label and kind.
labeledNodes :: SyntaxKind -> Text -> SyntaxNode -> [SyntaxNode]
labeledNodes k label n = [c | NodeElement c <- syntaxChildrenWithTokens n, syntaxLabel c == Just label, syntaxKind c == k]

-- | The first child token with a label and kind.
labeledToken :: SyntaxKind -> Text -> SyntaxNode -> Maybe SyntaxToken
labeledToken k label = listToMaybe . labeledTokens k label

-- | All child tokens with a label and kind.
labeledTokens :: SyntaxKind -> Text -> SyntaxNode -> [SyntaxToken]
labeledTokens k label n = [t | TokenElement t <- syntaxChildrenWithTokens n, tokenLabel t == Just label, tokenKind t == k]

-- Display ------------------------------------------------------------------------

-- | An indented dump of the tree, one element per line, as @Kind\@start..end@
-- with the text of tokens and the labels of children.
debugTree :: (SyntaxKind -> Text) -> SyntaxNode -> Text
debugTree name root = T.unlines (nodeLines 0 Nothing root [])
  where
    nodeLines depth label n acc =
      line depth label (name (syntaxKind n)) (syntaxRange n) Nothing
        : foldr (elementLines (depth + 1)) acc (syntaxChildrenWithTokens n)
    elementLines depth (NodeElement c) acc = nodeLines depth (syntaxLabel c) c acc
    elementLines depth (TokenElement t) acc = line depth (tokenLabel t) (name (tokenKind t)) (tokenRange t) (Just (tokenText t)) : acc
    line :: Int -> Maybe Text -> Text -> (Int, Int) -> Maybe Text -> Text
    line depth label kind (s, e) text =
      T.concat
        [ T.replicate (2 * depth) " "
        , maybe "" (<> ": ") label
        , kind
        , "@"
        , T.pack (show s)
        , ".."
        , T.pack (show e)
        , maybe "" (\t -> " " <> T.pack (show t)) text
        ]

-- Building -----------------------------------------------------------------------

-- | What a rule invocation contributes to the tree while parsing: nodes and
-- tokens with byte offsets and labels. Terminal matches are not recorded;
-- the gaps between children become text tokens when the tree is built.
data Child
  = CNode !SyntaxKind !Int !Int [Child] !(Maybe Text)
  | CToken !SyntaxKind !Int !Int !(Maybe Text)

-- | Label a child unless it already has a label.
setLabel :: Text -> Child -> Child
setLabel l c = case c of
  CNode k s e ks Nothing -> CNode k s e ks (Just l)
  CToken k s e Nothing -> CToken k s e (Just l)
  _ -> c

-- | The tree of a whole input. If the children are not a single node that
-- covers the input, they are wrapped in a node of the given kind.
syntaxRoot :: Text -> SyntaxKind -> [Child] -> SyntaxNode
syntaxRoot input k kids = SyntaxNode green 0 Nothing Nothing (Source input (lineIndex input))
  where
    len = TU.lengthWord8 input
    top = case kids of
      [c@(CNode _ 0 e _ _)] | e == len -> c
      _ -> CNode k 0 len kids Nothing
    green = case build input top of
      GreenNodeElement g -> g
      GreenTokenElement t -> GreenNode k (TU.lengthWord8 (gtText t)) [(Nothing, GreenTokenElement t)]

build :: Text -> Child -> GreenElement
build input c = case c of
  CToken k s e _ -> GreenTokenElement (GreenToken k (slice s e))
  CNode k s e kids _ -> GreenNodeElement (GreenNode k (e - s) (go s kids))
    where
      go pos [] = gap pos e
      go pos (x : xs) =
        let (xs', xe) = childRange x
         in gap pos xs' ++ [(childLabel x, build input x)] ++ go xe xs
  where
    slice s e = TU.takeWord8 (e - s) (TU.dropWord8 s input)
    gap s e
      | e > s = [(Nothing, GreenTokenElement (GreenToken textKind (slice s e)))]
      | otherwise = []
    childRange (CNode _ s e _ _) = (s, e)
    childRange (CToken _ s e _) = (s, e)
    childLabel (CNode _ _ _ _ l) = l
    childLabel (CToken _ _ _ l) = l
