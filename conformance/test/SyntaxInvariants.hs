-- | The invariants of a lossless syntax tree that "Peg.Runtime.Syntax"
-- promises (ADR 0019), checked on the trees of the conformance tests
-- (ADR 0081).
module SyntaxInvariants
  ( violations
  , concatViolations
  ) where

import Data.List (nub)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as B
import Peg.Runtime.Syntax

-- | What a tree of an input breaks of the invariants, as messages; empty
-- when it keeps them all:
--
-- * the ranges of the children of a node divide the range of the node, in
--   order and without gaps;
-- * the parent of a child node and of a token is the node, and the root
--   has no parent;
-- * the text of a node is the text of its tokens, joined, and is the input
--   in the range of the node;
-- * 'labeledTokens' and 'labeledNodes' are the children with the label and
--   the kind, out of 'syntaxChildrenWithTokens'.
--
-- The texts of all the nodes are compared only for inputs up to 64 KiB:
-- for deeply nested inputs, that takes time quadratic in the depth. For
-- longer inputs, the text of the root and of every token are compared, and
-- with the ranges, they give the texts of the other nodes.
violations :: Text -> SyntaxNode -> [String]
violations input root =
  [ "the root has a parent: " <> show root | Just _ <- [syntaxParent root] ]
    ++ [ "the text of the root is not the input" | syntaxText root /= input ]
    ++ [ "the text of " <> show t <> " is not the input in its range" | t <- syntaxTokens root, tokenText t /= slice (tokenRange t) ]
    ++ concatMap node (nodes root)
  where
    small = B.length bytes <= 65536
    bytes = TE.encodeUtf8 input
    slice (s, e) = TE.decodeUtf8 (B.take (e - s) (B.drop s bytes))
    node n =
      let kids = syntaxChildrenWithTokens n
          ranges = map rangeOf kids
          (s, e) = syntaxRange n
          starts = map fst ranges
          ends = map snd ranges
       in [ "the children of " <> show n <> " do not divide it: " <> show ranges
          | starts /= take (length ranges) (s : ends) || (if null ranges then s /= e else last ends /= e)
          ]
            ++ [ "the parent of " <> show c <> " is not " <> show n
               | NodeElement c <- kids
               , fmap syntaxRange (syntaxParent c) /= Just (syntaxRange n) || fmap syntaxKind (syntaxParent c) /= Just (syntaxKind n)
               ]
            ++ [ "the parent of " <> show t <> " is not " <> show n
               | TokenElement t <- kids
               , tokenParent t /= n
               ]
            ++ [ "the text of " <> show n <> " is not the text of its tokens"
               | small, syntaxText n /= T.concat (map tokenText (syntaxTokens n))
               ]
            ++ [ "the text of " <> show n <> " is not the input in its range"
               | small, syntaxText n /= slice (syntaxRange n)
               ]
            ++ [ "the text of " <> show n <> " is not the text of its children"
               | small, syntaxText n /= T.concat (map textOf kids)
               ]
            ++ [ "labeledTokens of " <> show l <> " in " <> show n
               | (k, l) <- labels [(tokenKind t, tokenLabel t) | TokenElement t <- kids]
               , labeledTokens k l n /= [t | TokenElement t <- kids, tokenLabel t == Just l, tokenKind t == k]
               ]
            ++ [ "labeledNodes of " <> show l <> " in " <> show n
               | (k, l) <- labels [(syntaxKind c, syntaxLabel c) | NodeElement c <- kids]
               , labeledNodes k l n /= [c | NodeElement c <- kids, syntaxLabel c == Just l, syntaxKind c == k]
               ]
    labels xs = nub [(k, l) | (k, Just l) <- xs]
    rangeOf = \e -> case e of
      NodeElement c -> syntaxRange c
      TokenElement t -> tokenRange t
    textOf = \e -> case e of
      NodeElement c -> syntaxText c
      TokenElement t -> tokenText t

-- | What the join of two trees breaks: its text is the texts of the trees,
-- joined, and the joined tree keeps the invariants of 'violations'.
concatViolations :: SyntaxKind -> SyntaxNode -> SyntaxNode -> [String]
concatViolations k a b =
  [ "the text of concatSyntax is not the texts joined"
  | syntaxText joined /= syntaxText a <> syntaxText b
  ]
    ++ violations (syntaxText a <> syntaxText b) joined
  where
    joined = concatSyntax k [a, b]

nodes :: SyntaxNode -> [SyntaxNode]
nodes n = n : concatMap nodes (syntaxChildren n)
