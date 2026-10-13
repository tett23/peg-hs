{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Inserting labels at the positions where the label check shows them to
-- be safe, and proposing recovery rules for labels (ADR 0054).
--
-- The candidates are the items of a sequence that come after an item that
-- always consumes input, as in the method Standard of Medeiros, Alvez and
-- Mascarenhas (2020); each one is kept only if
-- 'Peg.Grammar.Labels.labelSafeAt' shows its label to be safe. Every label
-- inserted therefore keeps the language of the grammar.
--
-- 'insertLabels' is what @peg-hs label@ runs: it returns the labels and the
-- source with them written in. Only @ ^name@ is inserted after each
-- expression; comments, spaces and line breaks are kept.
--
-- @
-- case insertLabels [] src of
--   Left diags -> mapM_ (TIO.putStrLn . renderDiagnostic \"Calc.hpeg\") diags
--   Right (labels, out) -> do
--     mapM_ (\\i -> print (insertionStart i, insertionName i)) labels
--     TIO.writeFile \"Calc.hpeg\" out
-- @
--
-- 'recoverProposals' is the other half, for the language server: for a
-- label without a recovery rule, the @%recover@ directive and a skeleton of
-- the recovery rule, whose value the author writes in place of a typed
-- hole.
module Peg.Grammar.LabelInsertion
  ( -- * Candidates
    Candidate (..)
  , labelCandidates
  , safeCandidates
  , coveredRules
    -- * Names
  , targetName
  , symbolNames
  , nameCandidates
    -- * Inserting
  , Insertion (..)
  , insertLabels
    -- * Recovery rules
  , Edit (..)
  , RecoverProposal (..)
  , recoverProposals
  , applyEdits
  ) where

import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Ord (Down (..))
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Assemble (isIdentChar)
import Peg.Grammar.Check (check)
import Peg.Grammar.Labels (labelSafeAt, matchesEmpty)
import Peg.Grammar.Parser (parseGrammar)
import qualified Peg.Grammar.SelfHostedSyntax as S
import Peg.Grammar.Templates (expandTemplates, templateNotes)
import Peg.Runtime (Pos (..))
import Peg.Runtime.Syntax

-- Candidates ------------------------------------------------------------------

-- | A position where a label could be inserted: an item of a rule, by the
-- path of 'Peg.Grammar.Labels.labelSafeAt', and its expression.
data Candidate = Candidate
  { candidateRule :: Text
  , candidatePath :: [(Int, Int)]
  , candidateExpr :: Expr
  -- ^ The expression of the item, with the captures @$@ around it.
  }
  deriving (Eq, Show)

-- | The candidates of a grammar, in source order, before the check of
-- safety. The first grammar is the grammar as parsed, the second the same
-- grammar with its templates expanded; the candidates are in the rules
-- that are not templates.
--
-- An item is a candidate when an item before it in its sequence cannot
-- match the empty string, it cannot match the empty string itself, its
-- expression (inside @$@) is a literal, a character class, @.@, a rule
-- reference, a group or @e+@, and it has no label. Items inside a
-- lookahead, inside an expression with a label whose recovery rule is
-- given by @%recover@, in a rule that such an expression calls
-- ('coveredRules'), and in recovery rules are not candidates. Neither are
-- the items of an alternative that always succeeds in the sense of
-- @peg-hs lint@ (options and repetitions that cannot throw a label) and has
-- alternatives after it, nor those of the rules it calls: a label there
-- would take away the warning unreachable-alternative of the linter.
labelCandidates :: Grammar -> Grammar -> [Candidate]
labelCandidates g0 g =
  concat
    [ concat
        [ sequenceCandidates (ruleName r0) [] i (zip (altItems a0) (altItems a))
        | (i, (a0, a)) <- zip [0 ..] (zip (ruleAlts r0) (ruleAlts r))
        , not (i + 1 < length (ruleAlts r0) && alwaysSucceeds throwing (altItems a0))
        ]
    | r0 <- grammarRules g0
    , null (ruleTemplateParams r0)
    , not (S.member (ruleName r0) excluded)
    , Just r <- [M.lookup (ruleName r0) expanded]
    ]
  where
    expanded = M.fromList [(ruleName r, r) | r <- grammarRules g]
    excluded = S.unions [coveredRules g, S.fromList [unLoc r | (_, r) <- grammarRecovers g], lintProtected g0]
    throwing = throwingRules (grammarRules g0)
    recovered = S.fromList [unLoc l | (l, _) <- grammarRecovers g]
    nullable = matchesEmpty g
    -- The items as parsed, which have the calls of templates, and as
    -- expanded, which tell whether they match the empty string.
    sequenceCandidates rule outer i items =
      concat
        [ [Candidate rule path e0 | after, not (nullable e), kind (uncapture e0)] ++ inside rule path e0 e
        | (j, (item0, item)) <- zip [0 ..] items
        , let path = outer ++ [(i, j)]
              after = any (not . nullable . itemExpr . snd) (take j items)
              e0 = itemExpr item0
              e = itemExpr item
        ]
    kind = \case
      ELit {} -> True
      EClass {} -> True
      EAny -> True
      ERef {} -> True
      EGroup _ -> True
      EPlus _ -> True
      _ -> False
    -- The candidates in the group that an item contains.
    inside rule path e0 e = case (e0, e) of
      (EGroup gs0, EGroup gs) -> concat [sequenceCandidates rule path k (zip is0 is) | (k, (is0, is)) <- zip [0 ..] (zip gs0 gs)]
      (EStar x0, EStar x) -> inside rule path x0 x
      (EPlus x0, EPlus x) -> inside rule path x0 x
      (EOpt x0, EOpt x) -> inside rule path x0 x
      (ECapture x0, ECapture x) -> inside rule path x0 x
      (EDiscard x0, EDiscard x) -> inside rule path x0 x
      (ELabel _ x0 l, ELabel _ x _)
        | S.member l recovered -> []
        | otherwise -> inside rule path x0 x
      _ -> []

-- Lint (ADR 0033) ------------------------------------------------------------
--
-- The warning unreachable-alternative of "Peg.Grammar.Lint" is given for
-- the alternatives after one that always succeeds: options and repetitions
-- of expressions that cannot throw a label. A label inside such an
-- alternative, or in a rule it calls, would take the warning away, so
-- neither is a candidate. The functions below follow those of the linter.

-- The rules that the alternatives that always succeed, and have
-- alternatives after them, call outside lookaheads, directly or through
-- other rules.
lintProtected :: Grammar -> S.Set Text
lintProtected g0 = reach S.empty (concatMap start (grammarRules g0))
  where
    throwing = throwingRules (grammarRules g0)
    rules = M.fromList [(ruleName r, r) | r <- grammarRules g0]
    start r = concat [concatMap (callsOutsideLookahead . itemExpr) (altItems a) | (i, a) <- zip [1 :: Int ..] (ruleAlts r), i < length (ruleAlts r), alwaysSucceeds throwing (altItems a)]
    reach seen = \case
      [] -> seen
      n : rest
        | S.member n seen -> reach seen rest
        | otherwise -> reach (S.insert n seen) (maybe [] (concatMap (concatMap (callsOutsideLookahead . itemExpr) . altItems) . ruleAlts) (M.lookup n rules) ++ rest)

callsOutsideLookahead :: Expr -> [Text]
callsOutsideLookahead = \case
  ERef _ n _ -> [n]
  EAnd _ -> []
  ENot _ -> []
  e -> concatMap callsOutsideLookahead (children e)

alwaysSucceeds :: S.Set Text -> [Item] -> Bool
alwaysSucceeds throwing = all (succeeds . itemExpr)
  where
    succeeds = \case
      EOpt x -> not (mayThrow throwing x)
      EStar x -> not (mayThrow throwing x)
      _ -> False

throwingRules :: [Rule] -> S.Set Text
throwingRules rules = go (S.fromList [ruleName r | r <- rules, any (mayThrow S.empty) (exprs r)])
  where
    exprs r = map itemExpr (concatMap altItems (ruleAlts r))
    names = S.fromList (map ruleName rules)
    go s =
      let s' = S.fromList [ruleName r | r <- rules, S.member (ruleName r) s || any (mayThrow s) (exprs r) || any (`S.notMember` names) (concatMap refsOf (exprs r))]
       in if s' == s then s else go s'

mayThrow :: S.Set Text -> Expr -> Bool
mayThrow throwing = \case
  ELabel {} -> True
  ERef _ n _ -> S.member n throwing
  ETemplate {} -> True
  EAnd _ -> False
  ENot _ -> False
  e -> any (mayThrow throwing) (children e)

uncapture :: Expr -> Expr
uncapture = \case
  ECapture x -> uncapture x
  x -> x

-- | The rules that an expression with a label whose recovery rule is given
-- by @%recover@ calls, directly or through other rules: their positions
-- are covered by the recovery, and a label there would throw past it. The
-- grammar has its templates expanded.
coveredRules :: Grammar -> S.Set Text
coveredRules g = reach S.empty (concatMap (concatMap itemCovered . altItems) (concatMap ruleAlts (grammarRules g)))
  where
    recovered = S.fromList [unLoc l | (l, _) <- grammarRecovers g]
    rules = M.fromList [(ruleName r, r) | r <- grammarRules g]
    itemCovered = exprCovered . itemExpr
    exprCovered = \case
      ELabel _ x l | S.member l recovered -> refsOf x
      e -> concatMap exprCovered (children e)
    reach seen = \case
      [] -> seen
      n : rest
        | S.member n seen -> reach seen rest
        | otherwise -> reach (S.insert n seen) (maybe [] (concatMap (concatMap (refsOf . itemExpr) . altItems) . ruleAlts) (M.lookup n rules) ++ rest)

-- The rules an expression refers to.
refsOf :: Expr -> [Text]
refsOf = \case
  ERef _ n _ -> [n]
  e -> concatMap refsOf (children e)

children :: Expr -> [Expr]
children = \case
  EGroup alts -> map itemExpr (concat alts)
  EStar x -> [x]
  EPlus x -> [x]
  EOpt x -> [x]
  EAnd x -> [x]
  ENot x -> [x]
  ECapture x -> [x]
  ELabel _ x _ -> [x]
  EDiscard x -> [x]
  ETemplate _ _ as _ -> as
  _ -> []

-- | The candidates whose label the check shows to be safe
-- ('Peg.Grammar.Labels.labelSafeAt'), in source order. The grammars are
-- those of 'labelCandidates'; the second must have passed
-- 'Peg.Grammar.Check.check'.
safeCandidates :: Grammar -> Grammar -> [Candidate]
safeCandidates g0 g = filter (\c -> safe (candidateRule c) (candidatePath c)) (labelCandidates g0 g)
  where
    safe = labelSafeAt g

-- Names -----------------------------------------------------------------------

-- | The names of literals of one symbol, for the names of labels.
symbolNames :: [(Char, Text)]
symbolNames =
  [ ('(', "lparen")
  , (')', "rparen")
  , ('[', "lbracket")
  , (']', "rbracket")
  , ('{', "lbrace")
  , ('}', "rbrace")
  , ('<', "lt")
  , ('>', "gt")
  , (',', "comma")
  , (';', "semi")
  , (':', "colon")
  , ('.', "dot")
  , ('=', "eq")
  , ('+', "plus")
  , ('-', "minus")
  , ('*', "star")
  , ('/', "slash")
  , ('\\', "backslash")
  , ('|', "bar")
  , ('&', "amp")
  , ('!', "bang")
  , ('?', "question")
  , ('#', "hash")
  , ('%', "percent")
  , ('^', "caret")
  , ('~', "tilde")
  , ('@', "at")
  , ('$', "dollar")
  , ('`', "backquote")
  , ('"', "dquote")
  , ('\'', "quote")
  ]

-- | What a label on an expression is named after: the rule of a reference,
-- the text of a literal of identifier characters, the name of a literal of
-- one symbol in 'symbolNames', @lit@ for other literals, @class@, @any@
-- and @group@; @e+@ and @$e@ are named after @e@.
targetName :: Expr -> Text
targetName = \case
  ERef _ n _ -> n
  ELit t _
    | Just (c, "") <- T.uncons t, Just n <- lookup c symbolNames -> n
    | not (T.null t) && T.all isIdentChar t -> t
    | otherwise -> "lit"
  EClass _ _ -> "class"
  EAny -> "any"
  EGroup _ -> "group"
  EPlus x -> targetName x
  ECapture x -> targetName x
  _ -> "lit"

-- | The names of the labels of candidates, in the order given:
-- @Rule_target@ ('targetName'), with @_2@, @_3@ and so on from the second
-- candidate of the same name, or when the name is a label, or a name of
-- @%recover@ or @%safe@, of the grammar already.
nameCandidates :: Grammar -> [Candidate] -> [(Candidate, Text)]
nameCandidates g = go (S.fromList reserved)
  where
    reserved =
      concatMap (concatMap (concatMap (labelsOf . itemExpr) . altItems) . ruleAlts) (grammarRules g)
        ++ [unLoc l | (l, _) <- grammarRecovers g]
        ++ map unLoc (grammarSafe g)
    labelsOf = \case
      ELabel _ x l -> l : labelsOf x
      e -> concatMap labelsOf (children e)
    go _ [] = []
    go used (c : cs) =
      let base = candidateRule c <> "_" <> targetName (candidateExpr c)
          name = fresh used base
       in (c, name) : go (S.insert name used) cs

-- The name, or the name with the first of _2, _3 and so on that is not
-- used.
fresh :: S.Set Text -> Text -> Text
fresh used base = go (base : [base <> "_" <> T.pack (show k) | k <- [2 :: Int ..]])
  where
    go = \case
      n : rest
        | S.member n used -> go rest
        | otherwise -> n
      [] -> base

-- Inserting -------------------------------------------------------------------

-- | A label to insert.
data Insertion = Insertion
  { insertionName :: Text
  , insertionRule :: Text
  -- ^ The rule of the expression.
  , insertionStart :: Loc
  -- ^ The start of the expression.
  , insertionEnd :: Loc
  -- ^ Just after the expression, where @ ^name@ is inserted.
  }
  deriving (Eq, Show)

-- | The safe labels of a grammar ('safeCandidates', named by
-- 'nameCandidates') and the source with them inserted. With rule names,
-- only the candidates in those rules are inserted. CRLF line breaks are
-- kept.
--
-- A grammar with an error (of the notation, of the templates or of
-- 'Peg.Grammar.Check.check') gives its errors, and so does a rule name
-- that is not in the grammar (@undefined rule R@, located at the start).
-- The result is parsed again and compared with the grammar with the labels
-- added; if they differ, which is a bug, an internal error is returned.
insertLabels :: [Text] -> Text -> Either [Diagnostic] ([Insertion], Text)
insertLabels only src = do
  g0 <- parseGrammar src
  g <- either (Left . templateNotes g0) Right (expandTemplates g0 >>= \g -> g <$ check g)
  let names = S.fromList (map ruleName (grammarRules g0))
  case [r | r <- only, not (S.member r names)] of
    [] -> pure ()
    missing -> Left [Diagnostic (Loc 1 1) ("undefined rule " <> r) | r <- missing]
  root <- either (const (Left [internalError "the syntax tree parser rejected the grammar"])) Right (S.parseSyntax src)
  let chosen = [c | c <- safeCandidates g0 g, null only || candidateRule c `elem` only]
      named = nameCandidates g chosen
  located <- maybe (Left [internalError "an expression was not found in the syntax tree"]) Right (mapM (locate root) named)
  let out = insertAt [(end, " ^" <> name) | (_, name, _, end) <- located] root
      expected = foldl (\acc (c, name) -> addLabel c name acc) g0 named
  case parseGrammar out of
    Right g' | eraseGrammar g' == eraseGrammar expected -> pure ()
    _ -> Left [internalError "inserting the labels would change the grammar"]
  pure ([Insertion name (candidateRule c) (loc root start) (loc root end) | (c, name, start, end) <- located], out)
  where
    internalError m = Diagnostic (Loc 1 1) ("internal error of label: " <> m)
    locate root (c, name) = do
      item <- itemNode root (candidateRule c) (candidatePath c)
      expr <- listToMaybe [n | n <- syntaxChildren item, kindOf n == "PrefixE"]
      start <- listToMaybe (significant expr)
      end <- listToMaybe (reverse (significant item))
      pure (c, name, fst (tokenRange start), snd (tokenRange end))

-- The tokens of a node that are not spaces or comments.
significant :: SyntaxNode -> [SyntaxToken]
significant n = [t | t <- syntaxTokens n, S.nameOfSyntaxKind (tokenKind t) `notElem` ["SpaceChar", "Comment"]]

kindOf :: SyntaxNode -> Text
kindOf = S.nameOfSyntaxKind . syntaxKind

loc :: SyntaxNode -> Int -> Loc
loc root o = let p = syntaxPos root o in Loc (posLine p) (posColumn p)

-- The definition of a rule in the syntax tree.
definitionNode :: SyntaxNode -> Text -> Maybe SyntaxNode
definitionNode root rule =
  listToMaybe
    [ n
    | n <- syntaxChildren root
    , kindOf n == "Declaration"
    , let es = syntaxChildrenWithTokens n
    , any (\case TokenElement t -> tokenText t == "<-"; _ -> False) es
    , take 1 [tokenText t | TokenElement t <- es, S.nameOfSyntaxKind (tokenKind t) == "Ident"] == [rule]
    ]

-- The node of the item at a path.
itemNode :: SyntaxNode -> Text -> [(Int, Int)] -> Maybe SyntaxNode
itemNode root rule path = do
  decl <- definitionNode root rule
  alts <- listToMaybe [n | n <- syntaxChildren decl, kindOf n == "Alts"]
  let ruleAltNodes = [n | n <- syntaxChildren alts, kindOf n == "Alt"] ++ [a | m <- syntaxChildren alts, kindOf m == "MoreAlt", a <- syntaxChildren m, kindOf a == "Alt"]
  case path of
    [] -> Nothing
    (i, j) : rest -> do
      alt <- index i (map itemsOf ruleAltNodes)
      item <- index j alt
      go item rest
  where
    go item = \case
      [] -> Just item
      (k, m) : rest -> do
        groupAlts <- firstGroup item
        let seqs = itemsOf groupAlts : [itemsOf g | g <- syntaxChildren groupAlts, kindOf g == "MoreGroup"]
        is <- index k seqs
        next <- index m is
        go next rest
    itemsOf n = [c | c <- syntaxChildren n, kindOf c == "Item"]
    -- The group of an item, through the operators around it.
    firstGroup n = listToMaybe (concatMap groups (syntaxChildren n))
    groups n
      | kindOf n == "GroupAlts" = [n]
      | kindOf n `elem` ["Item", "TemplateArgs", "CallArgs"] = []
      | otherwise = concatMap groups (syntaxChildren n)
    index n xs = case drop n xs of
      x : _ | n >= 0 -> Just x
      _ -> Nothing

-- The text of a syntax tree with texts inserted after the tokens that end
-- at the given byte offsets.
insertAt :: [(Int, Text)] -> SyntaxNode -> Text
insertAt texts root = T.concat (concatMap token (syntaxTokens root))
  where
    at = M.fromListWith (flip (<>)) texts
    token t = tokenText t : maybe [] pure (M.lookup (snd (tokenRange t)) at)

-- The grammar with a label on the expression of a candidate.
addLabel :: Candidate -> Text -> Grammar -> Grammar
addLabel c name g = g {grammarRules = map rule (grammarRules g)}
  where
    rule r
      | ruleName r == candidateRule c = r {ruleAlts = alts (candidatePath c) (ruleAlts r)}
      | otherwise = r
    alts path as = case path of
      (i, j) : rest -> [if i' == i then a {altItems = items j rest (altItems a)} else a | (i', a) <- zip [0 ..] as]
      [] -> as
    items j rest is = [if j' == j then it {itemExpr = expr rest (itemExpr it)} else it | (j', it) <- zip [0 :: Int ..] is]
    expr rest e = case rest of
      [] -> labelled e
      (k, m) : rest' -> case e of
        EGroup gs -> EGroup [if k' == k then items m rest' is else is | (k', is) <- zip [0 ..] gs]
        EStar x -> EStar (expr rest x)
        EPlus x -> EPlus (expr rest x)
        EOpt x -> EOpt (expr rest x)
        ECapture x -> ECapture (expr rest x)
        ELabel l x n -> ELabel l (expr rest x) n
        EDiscard x -> EDiscard (expr rest x)
        _ -> e
    labelled = \case
      ECapture x -> ECapture (labelled x)
      x -> ELabel (Loc 0 0) x name

-- A grammar without its locations.
eraseGrammar :: Grammar -> Grammar
eraseGrammar g =
  Grammar
    { grammarModule = erase (grammarModule g)
    , grammarStart = fmap erase (grammarStart g)
    , grammarEntries = map erase (grammarEntries g)
    , grammarExports = map erase (grammarExports g)
    , grammarEnv = fmap erase (grammarEnv g)
    , grammarTabstop = fmap erase (grammarTabstop g)
    , grammarNoMemo = map erase (grammarNoMemo g)
    , grammarLanguages = map erase (grammarLanguages g)
    , grammarSyntax = fmap (const z) (grammarSyntax g)
    , grammarTokens = map erase (grammarTokens g)
    , grammarTrivia = map erase (grammarTrivia g)
    , grammarInline = map erase (grammarInline g)
    , grammarRecovers = [(erase a, erase b) | (a, b) <- grammarRecovers g]
    , grammarSafe = map erase (grammarSafe g)
    , grammarVerbatim = map erase (grammarVerbatim g)
    , grammarRules = map rule (grammarRules g)
    }
  where
    z = Loc 0 0
    erase (Located _ x) = Located z x
    rule r = r {ruleLoc = z, ruleParams = [p {paramType = erase (paramType p)} | p <- ruleParams r], ruleType = erase (ruleType r), ruleAlts = map alt (ruleAlts r)}
    alt (Alt _ is a) = Alt z (map item is) (fmap erase a)
    item (Item _ b e) = Item z b (expr e)
    expr = \case
      ERef _ n as -> ERef z n (map erase as)
      EGroup gs -> EGroup (map (map item) gs)
      EStar e -> EStar (expr e)
      EPlus e -> EPlus (expr e)
      EOpt e -> EOpt (expr e)
      EAnd e -> EAnd (expr e)
      ENot e -> ENot (expr e)
      ECapture e -> ECapture (expr e)
      ELabel _ e l -> ELabel z (expr e) l
      EPred p c -> EPred p (erase c)
      ETemplate _ n as vs -> ETemplate z n (map expr as) (map erase vs)
      EDiscard e -> EDiscard (expr e)
      e -> e

-- Recovery rules --------------------------------------------------------------

-- | Text to insert at a location.
data Edit = Edit
  { editAt :: Loc
  , editText :: Text
  }
  deriving (Eq, Show)

-- | A recovery rule proposed for a label: the label, the range of the
-- labelled expression and its label, and the edits that add
-- @%recover label Recover_label@ after the last directive and the rule
-- @Recover_label@ after the rule of the label.
data RecoverProposal = RecoverProposal
  { proposalLabel :: Text
  , proposalRule :: Text
  -- ^ The name of the recovery rule: @Recover_label@, or with @_2@, @_3@
  -- and so on when a rule has that name.
  , proposalStart :: Loc
  -- ^ The start of the labelled expression.
  , proposalEnd :: Loc
  -- ^ Just after the name of the label.
  , proposalEdits :: [Edit]
  }
  deriving (Eq, Show)

-- | The recovery rules to propose for the labels of a grammar without an
-- error, in source order: one for each label in a rule that is not a
-- template, without @%recover@, outside the positions covered by a
-- recovery ('coveredRules' and the expressions of labels with
-- @%recover@), on an expression whose value has a type that can be told:
-- a rule reference (the type of the rule) or a literal, a character class
-- or @.@ (@()@).
--
-- The recovery rule skips @(!\'x\' .)*@ up to the first literal @\'x\'@ after
-- the labelled item in its sequence, or @(![\\n] .)*@ to the end of the
-- line without one. Its action is the typed hole @{ _ }@, which GHC reports
-- with its type at the line of the action.
recoverProposals :: Text -> Either [Diagnostic] [RecoverProposal]
recoverProposals src = do
  g0 <- parseGrammar src
  g <- either (Left . templateNotes g0) Right (expandTemplates g0 >>= \g -> g <$ check g)
  root <- either (const (Left [])) Right (S.parseSyntax src)
  let recovered = S.fromList [unLoc l | (l, _) <- grammarRecovers g0]
      covered = coveredRules g
      types = M.fromList [(ruleName r, unLoc (ruleType r)) | r <- grammarRules g0]
      ruleNames = S.fromList (map ruleName (grammarRules g0))
      nl = if "\r\n" `T.isInfixOf` src then "\r\n" else "\n"
      lastDirective = listToMaybe (reverse [n | n <- syntaxChildren root, kindOf n == "Directive"])
      labels =
        [ (r, path, x, name, next)
        | r <- grammarRules g0
        , null (ruleTemplateParams r)
        , not (S.member (ruleName r) covered)
        , (i, a) <- zip [0 ..] (ruleAlts r)
        , (path, x, name, next) <- sequenceLabels recovered [] i (altItems a)
        , not (S.member name recovered)
        ]
      proposal (r, path, x, name, next) = do
        ty <- case x of
          ERef _ n _ -> M.lookup n types
          ELit {} -> Just "()"
          EClass {} -> Just "()"
          EAny -> Just "()"
          _ -> Nothing
        item <- itemNode root (ruleName r) path
        labelPart <- listToMaybe (reverse [t | t <- significant item, S.nameOfSyntaxKind (tokenKind t) == "Ident", tokenText t == name])
        expr <- listToMaybe [n | n <- syntaxChildren item, kindOf n == "PrefixE"]
        start <- listToMaybe (significant expr)
        decl <- definitionNode root (ruleName r)
        declEnd <- listToMaybe (reverse (significant decl))
        dir <- lastDirective
        let recoverName = fresh ruleNames ("Recover_" <> name)
            skip = case next of
              Just lit -> "(!" <> lit <> " .)*"
              Nothing -> "(![\\n] .)*"
            Loc dl _ = loc root (snd (syntaxRange dir))
            dirEdit
              | dl < length (T.splitOn "\n" src) = Edit (Loc (dl + 1) 1) ("%recover " <> name <> " " <> recoverName <> nl)
              | otherwise = Edit (loc root (snd (syntaxRange dir))) (nl <> "%recover " <> name <> " " <> recoverName)
            ruleEdit = Edit (loc root (snd (tokenRange declEnd))) (T.concat [nl, nl, recoverName, " :: ", ty, nl, recoverName, " <- ", skip, " { _ }"])
        pure (RecoverProposal name recoverName (loc root (fst (tokenRange start))) (loc root (snd (tokenRange labelPart))) [dirEdit, ruleEdit])
  pure (mapMaybe proposal labels)

-- The labels of a sequence and the groups in it: the path of the item, the
-- labelled expression, the label and the first literal after the item,
-- as written. Groups inside a label with @%recover@ are covered.
sequenceLabels :: S.Set Text -> [(Int, Int)] -> Int -> [Item] -> [([(Int, Int)], Expr, Text, Maybe Text)]
sequenceLabels recovered outer i items =
  concat
    [ [(path, x, name, nextLiteral (drop (j + 1) items)) | Just (x, name) <- [labelOf (itemExpr item)]] ++ inside path (itemExpr item)
    | (j, item) <- zip [0 ..] items
    , let path = outer ++ [(i, j)]
    ]
  where
    labelOf = \case
      ELabel _ x name -> Just (x, name)
      ECapture x -> labelOf x
      EAnd x -> labelOf x
      ENot x -> labelOf x
      _ -> Nothing
    nextLiteral rest = listToMaybe [raw | it <- rest, ELit t raw <- [uncapture (itemExpr it)], not (T.null t)]
    inside path = \case
      EGroup gs -> concat [sequenceLabels recovered path k is | (k, is) <- zip [0 ..] gs]
      EStar x -> inside path x
      EPlus x -> inside path x
      EOpt x -> inside path x
      ECapture x -> inside path x
      EDiscard x -> inside path x
      ELabel _ x l
        | S.member l recovered -> []
        | otherwise -> inside path x
      _ -> []

-- | Apply edits to a text. The locations are those of the text before the
-- edits; edits at the same location are inserted in the order given.
applyEdits :: [Edit] -> Text -> Text
applyEdits edits src = foldl apply src (sortOn (Down . fst) (zip (map offset edits) [0 :: Int ..]) `zipWithEdits` edits)
  where
    ls = T.splitOn "\n" src
    offset (Edit (Loc l c) _) = sum (map ((+ 1) . T.length) (take (l - 1) ls)) + c - 1
    zipWithEdits order es = [(o, es !! k) | (o, k) <- order]
    apply t (o, Edit _ x) = T.take o t <> x <> T.drop o t
