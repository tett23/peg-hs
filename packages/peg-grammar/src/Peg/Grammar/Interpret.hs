{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | An interpreter of grammars that needs no GHC (ADR 0090).
--
-- The interpreter parses an input with a grammar without generating and
-- compiling a parser. It builds the parsers of the rules at run time from
-- the same functions of "Peg.Runtime.Internal" that generated code calls,
-- and runs them with the same entry functions. Left recursion,
-- memoisation, labels, recovery and the expected sets are therefore those
-- of a generated parser: for a grammar that it accepts, the interpreter
-- returns the same 'ParseError' as the generated @parse@, and the same
-- syntax tree as the generated @parseSyntax@ of the grammar with
-- @%syntax@.
--
-- It does not compute the values of the actions (the AST), which are
-- Haskell code: it reads neither the actions nor the verbatim blocks. A
-- grammar without @%syntax@ is interpreted as if it had @%syntax@, as
-- @peg-hs parse --format cst@ does; @%token@, @%trivia@ and @%inline@ are
-- taken as written.
--
-- Semantic predicates and the arguments of rules are Haskell code too.
-- The interpreter evaluates a small set of expressions:
--
-- * a predicate is @True@, @False@, or @term op term@, where @op@ is one of
--   @==@, @/=@, @<@, @<=@, @>@ and @>=@;
-- * a term is @atom@, @atom + atom@ or @atom - atom@;
-- * an atom is a non-negative decimal integer, the name of a parameter of
--   the rule that no binding on its left hides, or @_col@.
--
-- 'interpreter' rejects a grammar whose predicates are not of this form,
-- or that passes another expression to a parameter that a predicate reads
-- (directly or through other rules). A parameter that no predicate reads
-- is only used by actions: its arguments are not evaluated.
--
-- @
-- case parseGrammar src >>= \\g0 -> either (Left . templateNotes g0) Right (expandTemplates g0 >>= \\g -> check g >>= interpreter g) of
--   Left diags -> mapM_ (TIO.putStrLn . renderDiagnostic file) diags
--   Right ip -> case interpret ip Nothing input of
--     Left err -> TIO.putStrLn (renderParseError err)
--     Right tree -> TIO.putStr (debugTree (interpreterKindName ip) tree)
-- @
module Peg.Grammar.Interpret
  ( Interpreter
  , interpreter
  , interpret
  , interpretRecover
  , interpreterKindName
  , interpretWith
  ) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isSpace)
import qualified Data.Map as ML
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust, listToMaybe)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Peg.Grammar
import Peg.Grammar.Check (Analysis (..), Memoisation (..), childLabel, ruleMemoisation)
import Peg.Grammar.Types (unitRules)
import Peg.Runtime.Internal
  ( ArgTable
  , Config (..)
  , P
  , ParseError
  , ST
  , Stats
  , SyntaxError
  , SyntaxKind (..)
  , SyntaxNode
  , Table
  , andP
  , anyChar
  , captureS
  , choice
  , cls
  , defaultConfig
  , expecting
  , label
  , labeledMessageS
  , labeledS
  , lit
  , many1S
  , manyS
  , memo
  , memoArg
  , memoLR
  , newArgTable
  , newTable
  , node
  , nomemo
  , notP
  , optionalS
  , plain
  , predicate
  , runParser
  , runSyntaxRecover
  , syntaxRoot
  , token
  , voidS
  , withCol
  )
import Peg.Runtime.Syntax (Child, textKind)

-- | A grammar prepared for interpretation.
data Interpreter = Interpreter
  { ipPlans :: M.Map Text Plan
  , ipStart :: Text
  , ipKinds :: M.Map Int Text
  , ipTabstop :: Int
  }

-- How a rule is run: the function of "Peg.Runtime.Internal" that
-- memoises it, how many of its parameters are read, its display name
-- (@%expect@), how it appears in the tree, and its alternatives.
data Plan = Plan
  { planName :: Text
  , planMemo :: Memoisation
  , planArity :: Int
  , planExpect :: Maybe Text
  , planTree :: Tree
  , planAlts :: [[Step]]
  }

data Tree = TreeNode SyntaxKind | TreeToken SyntaxKind | TreeInline

-- An element of a sequence, with the label of its children.
data Step = Step (Maybe Text) Op

-- An expression, with its predicates and arguments interpreted.
data Op
  = OLit String String
  | OCls [(Char, Char)] String
  | OAny
  | -- | A call, with the arguments of the parameters that are read.
    ORef Text [Term]
  | OGroup [[Step]]
  | OStar Op
  | OPlus Op
  | OOpt Op
  | OAnd Op
  | ONot Op
  | OCapture Op
  | -- | A label, its message and its recovery rule.
    OLabel Text (Maybe Text) (Maybe Text) Op
  | OPred Bool Cond
  | ODiscard Op

-- An interpretable predicate.
data Cond = CConst Bool | CCmp (Int -> Int -> Bool) Term Term

-- An interpretable term.
data Term = TAtom Atom | TAdd Atom Atom | TSub Atom Atom

-- An atom: an integer, the parameter read at an index, or the column.
data Atom = ALit Int | AParam Int | ACol

-- The parameters visible at a place of a rule: the names of the parameters
-- that no binding on the left hides, with the index of each one among the
-- parameters read.
type Scope = M.Map Text (Maybe Int)

-- Preparing ---------------------------------------------------------------------

-- | Prepare a grammar whose templates are expanded and which passed
-- 'Peg.Grammar.Check.check', with its t'Analysis'. The diagnostics point
-- at the predicates and arguments that the interpreter cannot evaluate,
-- and at the parameters read by predicates whose type is not @Int@; they
-- are sorted by location. Errors inside a template are reported in its
-- body: 'Peg.Grammar.Templates.templateNotes' adds the call to them, as
-- for 'Peg.Grammar.Check.check'.
--
-- An error reads
-- @the interpreter cannot evaluate the predicate &{ isKeyword n }@ or
-- @the interpreter cannot evaluate the argument T.length e@.
interpreter :: Grammar -> Analysis -> Either [Diagnostic] Interpreter
interpreter g an = case M.elems (M.fromList (map keyed errors)) of
  [] -> Right ip
  es -> Left es
  where
    keyed d = ((diagLoc d, diagMessage d), d)
    rules = grammarRules g
    ruleMap = M.fromList [(ruleName r, r) | r <- rules]
    readSets = readParams rules
    readOf n = M.findWithDefault S.empty n readSets
    -- The parameters read, in the order of the rule.
    readOrder r = [paramName p | p <- ruleParams r, S.member (paramName p) (readOf (ruleName r))]
    -- The grammar is run as with %syntax (ADR 0036), whose rules without a
    -- type annotation have type () (ADR 0068).
    units = unitRules g {grammarSyntax = Just (fromMaybe (Loc 0 1 1) (grammarSyntax g))}
    inline = S.fromList (map unLoc (grammarInline g))
    tokens = S.fromList (map unLoc (grammarTokens g))
    kinds = zip [ruleName r | r <- rules, not (S.member (ruleName r) inline)] [2 ..]
    kindOf = M.fromList kinds
    errors =
      concatMap ruleErrors rules
        ++ [ Diagnostic (locOf (paramType p)) ("the interpreter cannot read the parameter " <> paramName p <> ", which is not of type Int")
           | r <- rules
           , p <- ruleParams r
           , S.member (paramName p) (readOf (ruleName r))
           , T.strip (unLoc (paramType p)) /= "Int"
           ]
    ruleErrors r =
      [ d
      | (scope, site) <- sites r
      , d <- case site of
          SitePred b c
            | isJust (parseCond (scopeOf r scope) (unLoc c)) -> []
            | otherwise -> [Diagnostic (locOf c) ("the interpreter cannot evaluate the predicate " <> (if b then "&{ " else "!{ ") <> T.strip (unLoc c) <> " }")]
          SiteArg callee k c
            | not (isReadArg callee k) -> []
            | isJust (parseTerm (scopeOf r scope) (unLoc c)) -> []
            | otherwise -> [Diagnostic (locOf c) ("the interpreter cannot evaluate the argument " <> T.strip (unLoc c))]
          SiteTemplate l -> [Diagnostic l "the interpreter needs a grammar whose templates are expanded"]
      ]
    isReadArg callee k = case M.lookup callee ruleMap of
      Just r' | Just p <- listToMaybe (drop k (ruleParams r')) -> S.member (paramName p) (readOf callee)
      _ -> False
    scopeOf r visible = M.fromList [(n, lookup n (zip (readOrder r) [0 ..])) | n <- S.toList visible]
    ip =
      Interpreter
        { ipPlans = M.fromList [(ruleName r, plan r) | r <- rules]
        , ipStart = analysisStart an
        , ipKinds = M.fromList [(k, n) | (n, k) <- kinds]
        , ipTabstop = maybe 0 unLoc (grammarTabstop g)
        }
    plan r =
      Plan
        { planName = ruleName r
        , planMemo = ruleMemoisation g an r
        , planArity = length (readOrder r)
        , planExpect = listToMaybe [unLoc d | (Located _ n, d) <- grammarExpects g, n == ruleName r]
        , planTree = case M.lookup (ruleName r) kindOf of
            Nothing -> TreeInline
            Just k
              | S.member (ruleName r) tokens -> TreeToken (SyntaxKind k)
              | otherwise -> TreeNode (SyntaxKind k)
        , planAlts = map (altSteps r) (ruleAlts r)
        }
    altSteps r a =
      [ Step (childLabel units i) (op (scopeOf r visible) (itemExpr i))
      | (visible, i) <- withVisible r (altItems a)
      ]
    op scope = \case
      ELit t o -> OLit (T.unpack t) (T.unpack o)
      EClass rs o -> OCls rs (T.unpack o)
      EAny -> OAny
      ERef _ n args ->
        let params = maybe [] ruleParams (M.lookup n ruleMap)
         in ORef n [term scope (unLoc a) | (p, a) <- zip params args, S.member (paramName p) (readOf n)]
      EGroup alts -> OGroup [[Step Nothing (op scope (itemExpr i)) | i <- is] | is <- alts]
      EStar x -> OStar (op scope x)
      EPlus x -> OPlus (op scope x)
      EOpt x -> OOpt (op scope x)
      EAnd x -> OAnd (op scope x)
      ENot x -> ONot (op scope x)
      ECapture x -> OCapture (op scope x)
      ELabel _ x l ->
        OLabel
          l
          (listToMaybe [unLoc m | (Located _ l', m) <- grammarMessages g, l' == l])
          (listToMaybe [unLoc x' | (Located _ l', x') <- grammarRecovers g, l' == l])
          (op scope x)
      EPred b c -> OPred b (fromMaybe (CConst False) (parseCond scope (unLoc c)))
      EDiscard x -> ODiscard (op scope x)
      ETemplate {} -> OPred True (CConst False)
    term scope c = fromMaybe (TAtom (ALit 0)) (parseTerm scope c)

-- The places of a rule's code that the interpreter reads, each with the
-- parameters visible there.
data Site
  = SitePred Bool (Located Text)
  | -- | An argument of a call: the rule called and the index of the
    -- parameter.
    SiteArg Text Int (Located Text)
  | SiteTemplate Loc

sites :: Rule -> [(Set Text, Site)]
sites r = concat [[(visible, s) | s <- exprSites (itemExpr i)] | a <- ruleAlts r, (visible, i) <- withVisible r (altItems a)]
  where
    exprSites = \case
      EPred b c -> [SitePred b c]
      ERef _ n args -> [SiteArg n k c | (k, c) <- zip [0 ..] args]
      ETemplate l _ _ _ -> [SiteTemplate l]
      EGroup alts -> concatMap (concatMap (exprSites . itemExpr)) alts
      EStar x -> exprSites x
      EPlus x -> exprSites x
      EOpt x -> exprSites x
      EAnd x -> exprSites x
      ENot x -> exprSites x
      ECapture x -> exprSites x
      ELabel _ x _ -> exprSites x
      EDiscard x -> exprSites x
      _ -> []

-- The items of an alternative, each with the parameters of the rule that
-- no binding on its left hides (ADR 0081). The code of an item sees the
-- bindings at the top of the sequence on its left, from inside a group too
-- (ADR 0082); the bindings inside a group are not visible (ADR 0083).
withVisible :: Rule -> [Item] -> [(Set Text, Item)]
withVisible r items = zip (scanl hide params items) items
  where
    params = S.fromList (map paramName (ruleParams r))
    hide s i = maybe s (`S.delete` s) (itemBind i)

-- The parameters that are read, by rule: those whose names appear in the
-- predicates of the rule, or in the arguments that it passes to the
-- parameters read of the rules it calls. A fixed point.
readParams :: [Rule] -> M.Map Text (Set Text)
readParams rules = go (M.fromList [(ruleName r, S.empty) | r <- rules])
  where
    paramsOf = M.fromList [(ruleName r, map paramName (ruleParams r)) | r <- rules]
    go cur =
      let next = M.fromList [(ruleName r, S.unions (map (siteReads cur) (sites r))) | r <- rules]
       in if next == cur then cur else go next
    siteReads cur (visible, site) = case site of
      SitePred _ c -> names visible c
      SiteArg callee k c
        | Just p <- listToMaybe (drop k (M.findWithDefault [] callee paramsOf))
        , S.member p (M.findWithDefault S.empty callee cur) ->
            names visible c
      _ -> S.empty
    names visible (Located l c) = S.fromList [n | Located _ n <- codeVariables l c, S.member n visible]

-- Expressions -------------------------------------------------------------------

data Tok = TInt Int | TName Text | TOp Text

tokens' :: Text -> Maybe [Tok]
tokens' t0 = go (T.unpack t0)
  where
    go s = case s of
      [] -> Just []
      c : rest
        | isSpace c -> go rest
        | isDigit c -> let (ds, more) = span isDigit s in (TInt (fromInteger (read ds)) :) <$> go more
        | isAlpha c || c == '_' -> let (xs, more) = span (\x -> isAlphaNum x || x == '_' || x == '\'') s in (TName (T.pack xs) :) <$> go more
        | otherwise -> case [o | o <- operators, T.unpack o == take (T.length o) s] of
            o : _ -> (TOp o :) <$> go (drop (T.length o) s)
            [] -> Nothing
    operators = ["==", "/=", "<=", ">=", "<", ">", "+", "-"]

-- The predicate of the code, if the interpreter can evaluate it.
parseCond :: Scope -> Text -> Maybe Cond
parseCond scope code =
  tokens' code >>= \case
    [TName "True"] -> Just (CConst True)
    [TName "False"] -> Just (CConst False)
    ts -> case break isCmp ts of
      (l, TOp o : r) | Just f <- lookup o comparisons -> CCmp f <$> termOf scope l <*> termOf scope r
      _ -> Nothing
  where
    isCmp = \case
      TOp o -> isJust (lookup o comparisons)
      _ -> False
    comparisons = [("==", (==)), ("/=", (/=)), ("<", (<)), ("<=", (<=)), (">", (>)), (">=", (>=))]

-- The term of the code, if the interpreter can evaluate it.
parseTerm :: Scope -> Text -> Maybe Term
parseTerm scope code = tokens' code >>= termOf scope

termOf :: Scope -> [Tok] -> Maybe Term
termOf scope = \case
  [a] -> TAtom <$> atomOf scope a
  [a, TOp "+", b] -> TAdd <$> atomOf scope a <*> atomOf scope b
  [a, TOp "-", b] -> TSub <$> atomOf scope a <*> atomOf scope b
  _ -> Nothing

atomOf :: Scope -> Tok -> Maybe Atom
atomOf scope = \case
  TInt k -> Just (ALit k)
  TName "_col" -> Just ACol
  TName n -> AParam <$> (M.lookup n scope >>= id)
  TOp _ -> Nothing

evalCond :: [Int] -> Int -> Cond -> Bool
evalCond args col = \case
  CConst b -> b
  CCmp f a b -> f (evalTerm args col a) (evalTerm args col b)

evalTerm :: [Int] -> Int -> Term -> Int
evalTerm args col = \case
  TAtom a -> atom a
  TAdd a b -> atom a + atom b
  TSub a b -> atom a - atom b
  where
    atom = \case
      ALit k -> k
      AParam k -> args !! k
      ACol -> col

-- Running -----------------------------------------------------------------------

-- The value of every parser: no value, and the children in the tree.
type R = ((), [Child])

-- The memo tables of the rules, by name.
data Store s = Store
  { stTables :: M.Map Text (Table s R)
  , stArgTables :: M.Map Text (ArgTable s [Int] R)
  }

newStore :: Interpreter -> ST s (Store s)
newStore ip =
  Store
    <$> traverse (const newTable) (M.filter ((`elem` [Memoised, MemoisedLeftRecursive]) . planMemo) (ipPlans ip))
    <*> traverse (const newArgTable) (M.filter ((== MemoisedWithArguments) . planMemo) (ipPlans ip))

-- The parsers of the rules, given the values of their parameters read.
-- The table refers to itself: it is lazy.
parsers :: Interpreter -> ML.Map Text ([Int] -> P (Store s) s R)
parsers ip = table
  where
    table = ML.map rule (ipPlans ip)
    rule pl =
      let name = T.unpack (planName pl)
          key = planName pl
          body args = wrapExpect pl (wrapTree pl (choice (map (sequenceOf args) (planAlts pl))))
          shared = case planMemo pl of
            Memoised -> memo ((M.! key) . stTables) name (body [])
            MemoisedLeftRecursive -> memoLR ((M.! key) . stTables) name (body [])
            _ -> nomemo name (body [])
       in case planMemo pl of
            MemoisedWithArguments -> \args -> memoArg ((M.! key) . stArgTables) name args (body args)
            NotMemoised | planArity pl > 0 -> \args -> nomemo name (body args)
            _ -> const shared
    wrapExpect pl = maybe id (expecting . T.unpack) (planExpect pl)
    wrapTree pl = case planTree pl of
      TreeNode k -> node k
      TreeToken k -> token k
      TreeInline -> id
    sequenceOf args steps = (\rs -> ((), concatMap snd rs)) <$> traverse (step args) steps
    step args (Step l o) = maybe id (label . T.unpack) l (parserOf args o)
    call n = table ML.! n
    parserOf args = \case
      OLit t o -> plain (lit t o)
      OCls rs o -> plain (cls rs o)
      OAny -> plain anyChar
      ORef n [] -> call n []
      ORef n terms -> withCol (\col -> call n (map (evalTerm args col) terms))
      OGroup alts -> choice (map (sequenceOf args) alts)
      OStar x -> voidS (manyS (parserOf args x))
      OPlus x -> voidS (many1S (parserOf args x))
      OOpt x -> voidS (optionalS (parserOf args x))
      OAnd x -> plain (andP (parserOf args x))
      ONot x -> plain (notP (parserOf args x))
      OCapture x -> voidS (captureS (parserOf args x))
      OLabel l msg rec x ->
        let recovery = fmap (\r -> voidS (call r [])) rec
         in case msg of
              Just m -> labeledMessageS (T.unpack l) (T.unpack m) recovery (parserOf args x)
              Nothing -> labeledS (T.unpack l) recovery (parserOf args x)
      OPred b c -> plain (predicate (\col -> evalCond args col c == b))
      ODiscard x -> voidS (parserOf args x)

-- The rule to start from, and the kind of the root of the tree.
startOf :: Interpreter -> Maybe Text -> (Text, SyntaxKind)
startOf ip entry = case M.lookup name (ipPlans ip) of
  Just pl
    | planArity pl == 0 -> (name, kind pl)
    | otherwise -> error ("Peg.Grammar.Interpret: the rule " <> T.unpack name <> " takes parameters")
  Nothing -> error ("Peg.Grammar.Interpret: no rule " <> T.unpack name)
  where
    name = fromMaybe (ipStart ip) entry
    kind pl = case planTree pl of
      TreeNode k -> k
      TreeToken k -> k
      TreeInline -> textKind

-- | Parse the input from a rule, the start rule when 'Nothing'. Any rule of
-- the grammar may be given, except one whose parameters are read by
-- predicates; another name is an error (a call of 'error'). The rule must
-- match the whole input, as with the generated @parse@ and @parseSyntax@.
interpret :: Interpreter -> Maybe Text -> Text -> Either ParseError SyntaxNode
interpret ip entry = fst . interpretWith defaultConfig ip entry

-- | Parse with recovery (ADR 0021), as the generated @parseSyntaxRecover@:
-- the tree, which covers every input, and the syntax errors recovered from.
interpretRecover :: Interpreter -> Maybe Text -> Text -> (SyntaxNode, [SyntaxError])
interpretRecover ip entry input =
  let (name, k) = startOf ip entry
      (tree, errs, _) = runSyntaxRecover (config ip defaultConfig) (newStore ip) ((parsers ip ML.! name) []) k input
   in (tree, errs)

-- | The name of a syntax kind: the rule name, or that of the text and error
-- kinds, as the generated @nameOfSyntaxKind@ of the grammar with
-- @%syntax@ gives it. The kinds are numbered in the same order.
interpreterKindName :: Interpreter -> SyntaxKind -> Text
interpreterKindName ip (SyntaxKind k) = case k of
  0 -> "TEXT"
  1 -> "ERROR"
  _ -> M.findWithDefault "UNKNOWN" k (ipKinds ip)

-- | 'interpret' with a configuration, returning the counters (for tests).
-- The tab stop of the configuration is replaced by that of @%tabstop@, as
-- in the generated @peg'parseWith@. A parameter that no predicate reads is
-- not part of the key of the memo table, so a grammar with such
-- parameters may evaluate fewer times than the generated parser.
interpretWith :: Config -> Interpreter -> Maybe Text -> Text -> (Either ParseError SyntaxNode, Stats)
interpretWith cfg ip entry input =
  let (name, k) = startOf ip entry
      (r, st) = runParser (config ip cfg) (newStore ip) ((parsers ip ML.! name) []) input
   in (fmap (syntaxRoot input k . snd) r, st)

config :: Interpreter -> Config -> Config
config ip cfg = cfg {cfgTabstop = ipTabstop ip}
