import LabelCheckCharSet
import AssembleChars

/-!
A model of packages/peg-grammar/src/Peg/Grammar/Labels.hs: `labelWarnings`,
`stripLabels`, `stripLabelsAs` and every function of the module they reach,
translated function by function. check-label-check.sh fixes the whole
Haskell source (label-check.source) and compares this model with the real
functions on the grammars of LabelCheckProbe.hs.

The translation keeps the Haskell names. The differences of form:
- `Data.Map` and `Data.Set` are lists. `M.fromList` keeps the last binding of
  a key (`findLast`); a set is a list read by membership. `M.fromListWith
  (flip (++))` of the callers keeps the calls of a rule in the order of the
  grammar, which is `refSites` filtered by name.
- `env' == env` of `fixpoint` compares two maps with the same keys, the rule
  names; `envEq` compares the binding of every rule name.
- `nullableRules` carries the proof that the known set only grows
  (`nullableGo`), which bounds its loop.
- `stronglyConnComp` of Data.Graph is replaced by `lrTables` and `componentOf`, which find
  the rules that reach themselves and the rules they reach and are reached
  from (see the premises).
- The recursion of `failed`, `succeeded`, `ruleFailed` and `ruleSucceeded`
  through the state monad is `run`, indexed by a fuel: `run (n + 1)` makes
  one step of each function and calls `run n`; `run 0` gives `none`.
  LabelCheckTermination proves that a fuel bounded by the grammar always
  suffices and that more fuel gives the same result, and defines
  `labelWarnings` with it.
- `simSeq` takes the items and reads their expressions, where the Haskell
  function takes `map itemExpr`; that is what bounds the recursion of
  `choice` over a group.
- Text is `String`, and the texts of the simulation (`Sim`) are lists of
  characters.

Premises (not proved here; the probe compares the results):
- The key of the visited set renders the matched items with `show`; the
  model renders them with `repr` (`preKey`). Derived `Show` and `Repr` are
  injective, so the two keys are equal exactly when the items are.
- `Data.Char.isAlpha` and `isAlphaNum` are the tables of AssembleChars
  (checked against GHC 9.10.3 by check-assemble-predicates.sh), and
  `isSpace` is `spaceRanges`, checked by check-label-check.sh.
- `stronglyConnComp` returns the strongly connected components of the graph
  of the rules (containers' Data.Graph); `componentOf` computes the same
  partition when the rule names are distinct. `assemble` and
  `resolveImports` reject a rule named twice, and `expandTemplates` names
  each instance with a name no rule has (TemplateExpansionWhole).
- Haskell's `Int` arithmetic of indices, depths and counters does not
  overflow; the model uses natural numbers.
-/

namespace PegHs.LabelCheck

/-! ## The grammar -/

structure Loc where
  file : Nat
  line : Nat
  col : Nat
  deriving BEq, DecidableEq, Repr

inductive Expr where
  | lit (t written : String)
  | cls (rs : List (HChar × HChar)) (written : String)
  | any
  | ref (l : Loc) (n : String) (args : List (Loc × String))
  | group (alts : List (List (Loc × Option String × Expr)))
  | star (x : Expr)
  | plus (x : Expr)
  | opt (x : Expr)
  | and (x : Expr)
  | not (x : Expr)
  | capture (x : Expr)
  | label (l : Loc) (x : Expr) (name : String)
  | pred (b : Bool) (c : Loc × String)
  | template (l : Loc) (n : String) (as : List Expr) (vs : List (Loc × String))
  | discard (x : Expr)
  deriving BEq, Repr

-- Item: its location, its binding, its expression.
abbrev Item := Loc × Option String × Expr

-- `other` stands for the fields that Labels.hs neither reads nor writes.
structure Alt where
  loc : Loc
  items : List Item
  other : List String
  deriving Repr

structure Rule where
  name : String
  params : List String
  alts : List Alt
  other : List String
  deriving Repr

structure Grammar where
  module : Loc × String
  start : Option (Loc × String)
  entries : List (Loc × String)
  recovers : List ((Loc × String) × (Loc × String))
  safe : List (Loc × String)
  messages : List ((Loc × String) × (Loc × String))
  rules : List Rule
  other : List String
  deriving Repr

structure Diagnostic where
  loc : Loc
  msg : String
  deriving DecidableEq, Repr

def findLast {α : Type} (xs : List (String × α)) (n : String) : Option α :=
  xs.foldl (fun acc p => if p.1 == n then some p.2 else acc) none

def lookupFirst {α : Type} (xs : List (String × α)) (n : String) : Option α :=
  (xs.find? (·.1 == n)).map (·.2)

def indexed {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | n, x :: xs => (n, x) :: indexed (n + 1) xs

theorem item_expr_lt {l : Loc} {b : Option String} {e : Expr} {is : List Item} :
    sizeOf e < sizeOf ((l, b, e) :: is) := by
  simp; omega

/-! ## Characters of Haskell code -/

open PegHs.AssembleChars (isAlpha isAlphaNum inRanges) in
def identChar (c : Char) : Bool := isAlphaNum c || c == '_' || c == '\''

open PegHs.AssembleChars (isAlpha) in
def identStart (c : Char) : Bool := isAlpha c || c == '_'

-- Data.Char.isSpace on the Unicode scalar values (GHC 9.10.3).
def spaceRanges : List (Nat × Nat) := [
  (0x9, 0xd),
  (0x20, 0x20),
  (0xa0, 0xa0),
  (0x1680, 0x1680),
  (0x2000, 0x200a),
  (0x202f, 0x202f),
  (0x205f, 0x205f),
  (0x3000, 0x3000),
]

def isSpace (c : Char) : Bool := PegHs.AssembleChars.inRanges spaceRanges c

-- T.strip
def strip (s : String) : String :=
  String.ofList (((s.toList.dropWhile isSpace).reverse.dropWhile isSpace).reverse)

-- T.split p
def splitOn (p : Char → Bool) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if p c then [] :: splitOn p cs
    else match splitOn p cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

-- identifiers
def identifiers (code : String) : List String :=
  ((splitOn (fun c => !identChar c) code.toList).filter
    (fun w => match w with | c :: _ => identStart c | [] => false)).map String.ofList

-- T.isInfixOf
def isInfix (needle hay : List Char) : Bool :=
  match hay with
  | [] => needle.isEmpty
  | _ :: rest => needle.isPrefixOf hay || isInfix needle rest

/-! ## The abstraction of an expression -/

structure Abs where
  consume : CharSet
  empty : CharSet
  sure : CharSet
  deriving DecidableEq, Repr

def bottom : Abs := ⟨CharSet.none, CharSet.none, CharSet.none⟩
def epsilon : Abs := ⟨CharSet.none, everything, everything⟩

def possible (a : Abs) : CharSet := a.consume.union a.empty

def andThen (x y : Abs) : Abs :=
  ⟨x.consume.union (x.empty.intersect y.consume), x.empty.intersect y.empty,
    if y.sure = everything then x.sure else CharSet.none⟩

def orElse (x y : Abs) : Abs :=
  ⟨x.consume.union y.consume, x.empty.union y.empty, x.sure.union y.sure⟩

abbrev Env := List (String × Abs)

structure Pass where
  env : Env
  notEmpty : Expr → CharSet
  notSure : Expr → CharSet

-- constantPred
def constantPred (positive : Bool) (c : Loc × String) : Option Bool :=
  let s := strip c.2
  if s == "True" then some positive
  else if s == "False" then some (!positive)
  else none

mutual
def exprAbs (p : Pass) : Expr → Abs
  | .lit t _ => match t.toList with
    | [] => epsilon
    | c :: rest => ⟨single c, CharSet.none, if rest.isEmpty then single c else CharSet.none⟩
  | .cls rs _ => let s := ranges rs; ⟨s, CharSet.none, s⟩
  | .any => ⟨anyChar, CharSet.none, anyChar⟩
  | .ref _ n _ => (findLast p.env n).getD bottom
  | .group alts => altsAbs p alts
  | .star x => ⟨(exprAbs p x).consume, everything, everything⟩
  | .plus x => let a := exprAbs p x; ⟨a.consume, a.empty, a.sure⟩
  | .opt x => ⟨(exprAbs p x).consume, everything, everything⟩
  | .and x => let a := exprAbs p x; ⟨CharSet.none, possible a, a.sure⟩
  | .not x => ⟨CharSet.none, p.notEmpty x, p.notSure x⟩
  | .capture x => exprAbs p x
  | .label _ x _ => exprAbs p x
  | .discard x => exprAbs p x
  | .template .. => ⟨everything, everything, CharSet.none⟩
  | .pred b c => match constantPred b c with
    | some true => epsilon
    | some false => bottom
    | none => ⟨CharSet.none, everything, CharSet.none⟩
termination_by e => sizeOf e

-- seqAbs
def seqAbs (p : Pass) : List Item → Abs
  | [] => epsilon
  | (_, _, e) :: is => andThen (exprAbs p e) (seqAbs p is)
termination_by is => sizeOf is

-- foldr orElse bottom (map (seqAbs p) alts)
def altsAbs (p : Pass) : List (List Item) → Abs
  | [] => bottom
  | a :: as => orElse (seqAbs p a) (altsAbs p as)
termination_by as => sizeOf as
end

def ruleAbs (p : Pass) (r : Rule) : Abs := altsAbs p (r.alts.map (·.items))

def envEq (rules : List Rule) (a b : Env) : Bool :=
  rules.all (fun r => findLast a r.name == findLast b r.name)

def fixpointGo (rules : List Rule) (mk : Env → Pass) (env : Env) (n : Nat) : Env :=
  let env' := rules.map (fun r => (r.name, ruleAbs (mk env) r))
  if envEq rules env' env || n > 1000 then env else fixpointGo rules mk env' (n + 1)
termination_by 1001 - n
decreasing_by simp at *; omega

def fixpoint (rules : List Rule) (mk : Env → Pass) : Env :=
  fixpointGo rules mk (rules.map (fun r => (r.name, bottom))) 0

def pass1 (env : Env) : Pass := ⟨env, fun _ => everything, fun _ => CharSet.none⟩

-- possible1 of abstractions
def possible1 (env1 : Env) (x : Expr) : CharSet := possible (exprAbs (pass1 env1) x)

def pass2 (env1 : Env) (env : Env) : Pass :=
  ⟨env, fun _ => everything, fun x => everything.minus (possible1 env1 x)⟩

-- sure2 of abstractions
def sure2 (env1 env2 : Env) (x : Expr) : CharSet := (exprAbs (pass2 env1 env2) x).sure

def pass3 (env1 env2 : Env) (env : Env) : Pass :=
  ⟨env, fun x => everything.minus (sure2 env1 env2 x), fun x => everything.minus (possible1 env1 x)⟩

def abstractions (rules : List Rule) : Env × Pass :=
  let env1 := fixpoint rules pass1
  let env2 := fixpoint rules (pass2 env1)
  let env3 := fixpoint rules (pass3 env1 env2)
  (env3, pass3 env1 env2 env3)

/-! ## Contexts -/

inductive Frame where
  | seq (items : List Item) (j : Nat)
  | alts (alts : List (Loc × List Item)) (i : Nat) (body : Bool)
  | star (x : Expr) (l : Loc)
  | plus (x : Expr) (l : Loc)
  | opt
  | and (l : Loc)
  | not (l : Loc)
  | label
  | capture
  deriving Repr

def frameKey : Frame → Nat × Nat
  | .seq _ j => (0, j)
  | .alts _ i _ => (1, i)
  | .star .. => (2, 0)
  | .plus .. => (3, 0)
  | .opt => (4, 0)
  | .and _ => (5, 0)
  | .not _ => (6, 0)
  | .label => (7, 0)
  | .capture => (8, 0)

structure Site where
  rule : String
  frames : List Frame
  loc : Loc
  expr : Expr
  deriving Repr

def isSite : Expr → Bool
  | .label .. => true
  | .ref .. => true
  | _ => false

def groupAlts (l : Loc) (gs : List (List Item)) : List (Loc × List Item) :=
  gs.map (fun is => (match is.head? with | some i => i.1 | none => l, is))

mutual
-- exprSites
def exprSites (rn : String) (fs : List Frame) (l : Loc) (e : Expr) : List Site :=
  (if isSite e then [⟨rn, fs, l, e⟩] else []) ++
  match e with
  | .group gs => altSites rn fs (groupAlts l gs) false 0 gs
  | .star x => exprSites rn (.star x l :: fs) l x
  | .plus x => exprSites rn (.plus x l :: fs) l x
  | .opt x => exprSites rn (.opt :: fs) l x
  | .and x => exprSites rn (.and l :: fs) l x
  | .not x => exprSites rn (.not l :: fs) l x
  | .capture x => exprSites rn (.capture :: fs) l x
  | .label _ x _ => exprSites rn (.label :: fs) l x
  | .discard x => exprSites rn (.capture :: fs) l x
  | _ => []
termination_by sizeOf e

-- The sites of the alternatives gs from the k-th on, under the frames outer.
def altSites (rn : String) (outer : List Frame) (galts : List (Loc × List Item)) (body : Bool) :
    Nat → List (List Item) → List Site
  | _, [] => []
  | k, is :: rest => itemSites rn outer galts body k is 0 is ++ altSites rn outer galts body (k + 1) rest
termination_by _ gs => sizeOf gs

-- itemSites (FSeq is j : FAlts galts k body : outer), for the items from the j-th on.
def itemSites (rn : String) (outer : List Frame) (galts : List (Loc × List Item)) (body : Bool)
    (k : Nat) (is : List Item) : Nat → List Item → List Site
  | _, [] => []
  | j, (l, _, e) :: rest =>
    exprSites rn (.seq is j :: .alts galts k body :: outer) l e ++
      itemSites rn outer galts body k is (j + 1) rest
termination_by _ items => sizeOf items
end

def sites (r : Rule) : List Site :=
  altSites r.name [] (r.alts.map (fun a => (a.loc, a.items))) true 0 (r.alts.map (·.items))

/-! ## Removing labels -/

mutual
def unlabelExpr : Expr → Expr
  | .label _ x _ => unlabelExpr x
  | .group alts => .group (unlabelAlts alts)
  | .star x => .star (unlabelExpr x)
  | .plus x => .plus (unlabelExpr x)
  | .opt x => .opt (unlabelExpr x)
  | .and x => .and (unlabelExpr x)
  | .not x => .not (unlabelExpr x)
  | .capture x => .capture (unlabelExpr x)
  | .discard x => .discard (unlabelExpr x)
  | .template l n as cs => .template l n (unlabelList as) cs
  | e => e
termination_by e => sizeOf e

def unlabelItems : List Item → List Item
  | [] => []
  | (l, b, e) :: is => (l, b, unlabelExpr e) :: unlabelItems is
termination_by is => sizeOf is

def unlabelAlts : List (List Item) → List (List Item)
  | [] => []
  | a :: as => unlabelItems a :: unlabelAlts as
termination_by as => sizeOf as

def unlabelList : List Expr → List Expr
  | [] => []
  | e :: es => unlabelExpr e :: unlabelList es
termination_by es => sizeOf es
end

def unlabelGrammar (g : Grammar) : Grammar :=
  { g with rules := g.rules.map (fun r => { r with alts := r.alts.map (fun a => { a with items := unlabelItems a.items }) }) }

def unlabelFrames (fs : List Frame) : List Frame :=
  fs.flatMap fun f => match f with
    | .label => []
    | .seq items j => [.seq (unlabelItems items) j]
    | .alts alts i body => [.alts (alts.map (fun p => (p.1, unlabelItems p.2))) i body]
    | .star x l => [.star (unlabelExpr x) l]
    | .plus x l => [.plus (unlabelExpr x) l]
    | f => [f]

/-! ## Plain expressions and code -/

def noLoc : Loc := ⟨0, 0, 0⟩

mutual
def plainExpr : Expr → Expr
  | .ref _ n args => .ref noLoc n (args.map (fun a => (noLoc, a.2)))
  | .group alts => .group (plainAlts alts)
  | .star x => .star (plainExpr x)
  | .plus x => .plus (plainExpr x)
  | .opt x => .opt (plainExpr x)
  | .and x => .and (plainExpr x)
  | .not x => .not (plainExpr x)
  | .capture x => .capture (plainExpr x)
  | .label _ x _ => plainExpr x
  | .discard x => .discard (plainExpr x)
  | .pred b c => .pred b (noLoc, c.2)
  | .template _ n as vs => .template noLoc n (plainList as) (vs.map (fun v => (noLoc, v.2)))
  | e => e
termination_by e => sizeOf e

def plainItems : List Item → List Item
  | [] => []
  | (_, _, e) :: is => (noLoc, none, plainExpr e) :: plainItems is
termination_by is => sizeOf is

def plainAlts : List (List Item) → List (List Item)
  | [] => []
  | a :: as => plainItems a :: plainAlts as
termination_by as => sizeOf as

def plainList : List Expr → List Expr
  | [] => []
  | e :: es => plainExpr e :: plainList es
termination_by es => sizeOf es
end

mutual
-- exprCodes
def exprCodes : Expr → List String
  | .ref _ _ args => args.map (·.2)
  | .pred _ c => [c.2]
  | .group alts => altsCodes alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => exprCodes x
  | .label _ x _ => exprCodes x
  | .template _ _ as _ => listCodes as
  | _ => []
termination_by e => sizeOf e

def itemsCodes : List Item → List String
  | [] => []
  | (_, _, e) :: is => exprCodes e ++ itemsCodes is
termination_by is => sizeOf is

def altsCodes : List (List Item) → List String
  | [] => []
  | a :: as => itemsCodes a ++ altsCodes as
termination_by as => sizeOf as

def listCodes : List Expr → List String
  | [] => []
  | e :: es => exprCodes e ++ listCodes es
termination_by es => sizeOf es
end

mutual
-- exprMentions isTemplateOrEnv
def mentionsTemplateOrEnv (e : Expr) : Bool :=
  isTemplateOrEnv e ||
  match e with
  | .group alts => altsMention alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => mentionsTemplateOrEnv x
  | .label _ x _ => mentionsTemplateOrEnv x
  | .template _ _ as _ => listMention as
  | _ => false
termination_by sizeOf e

def itemsMention : List Item → Bool
  | [] => false
  | (_, _, e) :: is => mentionsTemplateOrEnv e || itemsMention is
termination_by is => sizeOf is

def altsMention : List (List Item) → Bool
  | [] => false
  | a :: as => itemsMention a || altsMention as
termination_by as => sizeOf as

def listMention : List Expr → Bool
  | [] => false
  | e :: es => mentionsTemplateOrEnv e || listMention es
termination_by es => sizeOf es

def isTemplateOrEnv (e : Expr) : Bool :=
  match e with
  | .template .. => true
  | e => (exprCodes e).any (fun c => (identifiers c).contains "_env")
end

def itemBind (i : Item) : Option String := i.2.1
def itemExpr (i : Item) : Expr := i.2.2
def itemLoc (i : Item) : Loc := i.1

def readsAny (names : List String) (code : String) : Bool :=
  (identifiers code).any (fun w => names.contains w)

-- commonPrefix
def commonPrefixGo (n : Nat) (bx by' : List (Option String)) : List Item → List Item → Nat
  | a :: as, b :: bs =>
    if plainExpr (itemExpr a) == plainExpr (itemExpr b) &&
        (bx == by' || !((exprCodes (itemExpr a)).any (readsAny ((bx ++ by').filterMap id)))) then
      commonPrefixGo (n + 1) (itemBind a :: bx) (itemBind b :: by') as bs
    else n
  | _, _ => n

def commonPrefix (xs ys : List Item) : Nat := commonPrefixGo 0 [] [] xs ys

/-! ## Calls across rules (ADR 0038) -/

def paren (a : String) : String :=
  let s := strip a
  if s.toList.all identChar && !s.isEmpty then s else "(" ++ s ++ ")"

-- paramMap: Map Text Text as an association list, last binding first in lookup.
def paramMap (r : Rule) (args : List (Loc × String)) : Option (List (String × String)) :=
  if r.params.length == args.length then some (r.params.zip (args.map (fun a => paren a.2))) else none

def pmMember (pm : List (String × String)) (w : String) : Bool := (findLast pm w).isSome

-- rewrite
theorem length_dropWhile_le' (p : Char → Bool) : ∀ (l : List Char), (l.dropWhile p).length ≤ l.length
  | [] => by simp
  | c :: cs => by
    simp only [List.dropWhile]
    cases p c
    · simp
    · have := length_dropWhile_le' p cs; simp; omega

theorem dropWhile_lt {p : Char → Bool} {c : Char} {cs : List Char} (h : p c = true) :
    ((c :: cs).dropWhile p).length < (c :: cs).length := by
  simp only [List.dropWhile, h]
  exact Nat.lt_succ_of_le (length_dropWhile_le' _ _)

set_option linter.unusedVariables false in
def rewrite (pm : List (String × String)) (t : List Char) : List Char :=
  match t with
  | [] => []
  | c :: cs =>
    if h : identChar c then
      let w := (c :: cs).takeWhile identChar
      ((findLast pm (String.ofList w)).getD (String.ofList w)).toList ++
        rewrite pm ((c :: cs).dropWhile identChar)
    else
      (c :: cs).takeWhile (fun c => !identChar c) ++
        rewrite pm ((c :: cs).dropWhile (fun c => !identChar c))
termination_by t.length
decreasing_by
  · exact dropWhile_lt h
  · exact dropWhile_lt (p := fun c => !identChar c) (by simpa using h)

def substCode (pm : List (String × String)) (c : Loc × String) : Option (Loc × String) :=
  let ws := identifiers c.2
  if !(ws.any (pmMember pm)) then some c
  else if ["let", "where", "case", "of", "do"].any (fun k => ws.contains k) ||
      ["\\", "->", "<-"].any (fun s => isInfix s.toList c.2.toList) then none
  else some (c.1, String.ofList (rewrite pm c.2.toList))

mutual
def substExpr (pm : List (String × String)) : Expr → Option Expr
  | .ref l n as => (as.mapM (substCode pm)).map (.ref l n)
  | .pred b c => (substCode pm c).map (.pred b)
  | .group alts => (substAlts pm alts).map .group
  | .star x => (substExpr pm x).map .star
  | .plus x => (substExpr pm x).map .plus
  | .opt x => (substExpr pm x).map .opt
  | .and x => (substExpr pm x).map .and
  | .not x => (substExpr pm x).map .not
  | .capture x => (substExpr pm x).map .capture
  | .label l x n => (substExpr pm x).map (fun x' => .label l x' n)
  | .discard x => (substExpr pm x).map .discard
  | .template l n as vs =>
    match substList pm as, vs.mapM (substCode pm) with
    | some as', some vs' => some (.template l n as' vs')
    | _, _ => none
  | e => some e
termination_by e => sizeOf e

def substItem (pm : List (String × String)) : Item → Option Item
  | (l, b, e) =>
    if (match b with | some n => pmMember pm n | none => false) then none
    else (substExpr pm e).map (fun e' => (l, b, e'))
termination_by i => sizeOf i

def substItemsL (pm : List (String × String)) : List Item → Option (List Item)
  | [] => some []
  | i :: is => match substItem pm i, substItemsL pm is with
    | some i', some is' => some (i' :: is')
    | _, _ => none
termination_by is => sizeOf is

def substAlts (pm : List (String × String)) : List (List Item) → Option (List (List Item))
  | [] => some []
  | a :: as => match substItemsL pm a, substAlts pm as with
    | some a', some as' => some (a' :: as')
    | _, _ => none
termination_by as => sizeOf as

def substList (pm : List (String × String)) : List Expr → Option (List Expr)
  | [] => some []
  | e :: es => match substExpr pm e, substList pm es with
    | some e', some es' => some (e' :: es')
    | _, _ => none
termination_by es => sizeOf es
end

-- substItems
def substItems (pm : List (String × String)) (is : List Item) : Option (List Item) :=
  substItemsL pm is

/-! ## The analysis of a grammar -/

def maxPrefix : Nat := 8
def maxLifts : Nat := 3
def maxCode' : Nat := 64
def expandDepth : Nat := 8
def maxExpansions : Nat := 64
def maxKnown : Nat := 4

mutual
def nullableExpr (known : List String) : Expr → Bool
  | .lit t _ => t.isEmpty
  | .cls .. => false
  | .any => false
  | .ref _ n _ => known.contains n
  | .group alts => nullableAlts known alts
  | .plus x => nullableExpr known x
  | .capture x => nullableExpr known x
  | .label _ x _ => nullableExpr known x
  | .discard x => nullableExpr known x
  | _ => true
termination_by e => sizeOf e

-- all (nullableExpr known . itemExpr)
def nullableItems (known : List String) : List Item → Bool
  | [] => true
  | (_, _, e) :: is => nullableExpr known e && nullableItems known is
termination_by is => sizeOf is

-- any (all (nullableExpr known . itemExpr))
def nullableAlts (known : List String) : List (List Item) → Bool
  | [] => false
  | a :: as => nullableItems known a || nullableAlts known as
termination_by as => sizeOf as
end

def nullStep (rules : List Rule) (known : List String) : List String :=
  (rules.filter (fun r => r.alts.any (fun a => nullableItems known a.items))).map (·.name)

def Sub (a b : List String) : Prop := ∀ x ∈ a, x ∈ b

mutual
theorem nullableExpr_mono {k k' : List String} (h : Sub k k') :
    (e : Expr) → nullableExpr k e = true → nullableExpr k' e = true
  | .lit .., hn => by simpa [nullableExpr] using hn
  | .cls .., hn | .any, hn => by simp [nullableExpr] at hn
  | .ref _ n _, hn => by
    simp [nullableExpr] at hn ⊢
    exact h n hn
  | .group alts, hn => by
    simp only [nullableExpr] at hn ⊢
    exact nullableAlts_mono h alts hn
  | .plus x, hn | .capture x, hn | .discard x, hn => by
    simp only [nullableExpr] at hn ⊢
    exact nullableExpr_mono h x hn
  | .label _ x _, hn => by
    simp only [nullableExpr] at hn ⊢
    exact nullableExpr_mono h x hn
  | .star _, _ | .opt _, _ | .and _, _ | .not _, _ | .pred .., _ | .template .., _ => by
    simp [nullableExpr]
termination_by e => sizeOf e

theorem nullableItems_mono {k k' : List String} (h : Sub k k') :
    (is : List Item) → nullableItems k is = true → nullableItems k' is = true
  | [], _ => by simp [nullableItems]
  | (_, _, e) :: is, hn => by
    simp only [nullableItems, Bool.and_eq_true] at hn ⊢
    exact ⟨nullableExpr_mono h e hn.1, nullableItems_mono h is hn.2⟩
termination_by is => sizeOf is

theorem nullableAlts_mono {k k' : List String} (h : Sub k k') :
    (as : List (List Item)) → nullableAlts k as = true → nullableAlts k' as = true
  | [], hn => by simp [nullableAlts] at hn
  | a :: as, hn => by
    simp only [nullableAlts, Bool.or_eq_true] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (nullableItems_mono h a hn)
    · exact Or.inr (nullableAlts_mono h as hn)
termination_by as => sizeOf as
end

theorem nullStep_mono {rules : List Rule} {k k' : List String} (h : Sub k k') :
    Sub (nullStep rules k) (nullStep rules k') := by
  intro x hx
  simp only [nullStep, List.mem_map, List.mem_filter, List.any_eq_true] at hx ⊢
  obtain ⟨r, ⟨hr, a, ha, hn⟩, rfl⟩ := hx
  exact ⟨r, ⟨hr, a, ha, nullableItems_mono h _ hn⟩, rfl⟩

def setEq (a b : List String) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

theorem nullStep_names (rules : List Rule) (k : List String) :
    Sub (nullStep rules k) (rules.map (·.name)) := by
  intro x hx
  simp only [nullStep, List.mem_map, List.mem_filter] at hx ⊢
  obtain ⟨r, ⟨hr, _⟩, rfl⟩ := hx
  exact ⟨r, hr, rfl⟩

theorem filter_length_le {α : Type} (l : List α) (p q : α → Bool) (hpq : ∀ y, p y = true → q y = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    by_cases hp : p y = true
    · have hq := hpq y hp
      simp [hp, hq]; exact ih
    · by_cases hq : q y = true
      · simp [hp, hq]; omega
      · simp [hp, hq]; exact ih

theorem filter_length_lt {α : Type} (l : List α) (p q : α → Bool) (hpq : ∀ y, p y = true → q y = true)
    (x : α) (hx : x ∈ l) (hq : q x = true) (hp : p x = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    have hle := filter_length_le ys p q hpq
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp [hp, hq]; omega
    · have := ih hx'
      by_cases hpy : p y = true
      · have hqy := hpq y hpy; simp [hpy, hqy]; omega
      · by_cases hqy : q y = true
        · simp [hpy, hqy]; omega
        · simp [hpy, hqy]; omega

theorem missing_lt {names a b : List String} (hab : Sub a b) (hbn : Sub b names)
    (hne : setEq b a = false) :
    (names.filter (fun x => !b.contains x)).length < (names.filter (fun x => !a.contains x)).length := by
  have hx : ∃ x ∈ b, x ∉ a := by
    simp only [setEq, Bool.and_eq_false_iff, List.all_eq_false, List.contains_iff_mem] at hne
    rcases hne with ⟨x, hx, hxa⟩ | ⟨x, hx, hxb⟩
    · exact ⟨x, hx, by simpa using hxa⟩
    · exact absurd (hab x hx) (by simpa using hxb)
  obtain ⟨x, hxb, hxa⟩ := hx
  apply filter_length_lt names _ _ _ x (hbn x hxb) (by simpa using hxa) (by simpa using hxb)
  intro y hy
  simp at hy ⊢
  exact fun h => hy (hab y h)

-- The loop of nullableRules, from a set that the step does not shrink.
set_option linter.unusedVariables false in
def nullableGo (rules : List Rule) (known : List String) (h : Sub known (nullStep rules known)) :
    List String :=
  let next := nullStep rules known
  if hne : setEq next known then known
  else nullableGo rules next (nullStep_mono h)
termination_by ((rules.map (·.name)).filter (fun x => !known.contains x)).length
decreasing_by
  exact missing_lt (names := rules.map (·.name)) h (nullStep_names rules known) (by simpa using hne)

def nullableRules (rules : List Rule) : List String :=
  nullableGo rules [] (fun _ h => by simp at h)

def leftCallsCalls (known : List String) : Expr → List String
  | .ref _ n _ => [n]
  | .group alts => leftCallsAlts known alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => leftCallsCalls known x
  | .label _ x _ => leftCallsCalls known x
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  leftCallsAlts (known : List String) : List (List Item) → List String
    | [] => []
    | a :: as => leftCallsGo known a ++ leftCallsAlts known as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  leftCallsGo (known : List String) : List Item → List String
    | [] => []
    | (_, _, e) :: is => leftCallsCalls known e ++ (if nullableExpr known e then leftCallsGo known is else [])
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega

def leftCalls (known : List String) (items : List Item) : List String :=
  leftCallsCalls.leftCallsGo known items

-- The rules reachable from n by at least one edge: the rules the edges of
-- the rules in acc lead to, added until none is new.
def reachStep (succ : String → List String) (acc : List String) : List String :=
  acc ++ (acc.flatMap succ).filter (fun m => !acc.contains m)

def reachIter (succ : String → List String) : Nat → List String → List String
  | 0, acc => acc
  | k + 1, acc =>
    let next := reachStep succ acc
    if next.length == acc.length then acc else reachIter succ k next

-- The tables of leftRecursion: the rule names, the left calls of each
-- alternative of each rule, the rules each rule reaches, and the component
-- of each rule in a cycle.
structure LrTables where
  names : List String
  calls : List (String × List (List String))
  reach : List (String × List String)
  comps : List (String × Option (List String))

-- The edges of a rule in the graph of stronglyConnComp: its left calls of rules.
def succOf (names : List String) (calls : List (String × List (List String))) (n : String) : List String :=
  match lookupFirst calls n with
  | some cs => cs.flatten.filter (fun m => names.contains m)
  | none => []

def reachOf (reach : List (String × List String)) (n : String) : List String :=
  (lookupFirst reach n).getD []

-- The strongly connected component of n, when n is in a cycle.
def componentOf (names : List String) (reach : List (String × List String)) (n : String) :
    Option (List String) :=
  if (reachOf reach n).contains n then
    some (names.filter (fun m => (reachOf reach n).contains m && (reachOf reach m).contains n))
  else none

def lrTables (rules : List Rule) : LrTables :=
  let nullable := nullableRules rules
  let names := rules.map (·.name)
  let calls := rules.map (fun r => (r.name, r.alts.map (fun a => leftCalls nullable a.items)))
  let reach := names.map (fun n => (n, reachIter (succOf names calls) names.length (succOf names calls n)))
  ⟨names, calls, reach, names.map (fun n => (n, componentOf names reach n))⟩

def componentIn (t : LrTables) (n : String) : Option (List String) := (lookupFirst t.comps n).getD none

-- growing of leftRecursion: the alternative i of n calls a rule of its component.
def growingIn (t : LrTables) (n : String) (i : Nat) : Bool :=
  match componentIn t n, findLast t.calls n with
  | some comp, some cs => match cs[i]? with
    | some c => c.any (fun m => comp.contains m)
    | none => false
  | _, _ => false

def isDirectIn (t : LrTables) (r : Rule) : Bool :=
  match componentIn t r.name with
  | some comp =>
    (comp.all (· == r.name) && comp.contains r.name) &&
      (indexed 0 r.alts).all (fun (i, a) =>
        !growingIn t r.name i ||
          match a.items with
          | (_, _, .ref _ n []) :: _ => n == r.name
          | _ => false)
  | none => false

def leftRecursion (rules : List Rule) : List String × List String × (String → Nat → Bool) :=
  let t := lrTables rules
  let inLr := t.names.filter (fun n => (componentIn t n).isSome)
  let direct := (rules.filter (fun r => inLr.contains r.name && isDirectIn t r)).map (·.name)
  let other := inLr.filter (fun n => !direct.contains n)
  (direct, other, growingIn t)

structure Ctx where
  pass : Pass
  refSites : List Site
  entries : List String
  recovery : List String
  directLr : List String
  otherLr : List String
  growing : String → Nat → Bool
  rules : List (String × Rule)
  expandable : List String

def startName (g : Grammar) : String :=
  match g.start, g.rules with
  | some s, _ => s.2
  | none, r :: _ => r.name
  | none, [] => ""

def isRef : Expr → Bool
  | .ref .. => true
  | _ => false

def context (g : Grammar) : Ctx :=
  let rules := g.rules
  let lr := leftRecursion rules
  let expandable := fun (r : Rule) => !(r.alts.any (fun a => itemsMention a.items))
  { pass := (abstractions rules).2
    refSites := (rules.flatMap sites).filter (fun s => isRef s.expr)
    entries := startName g :: g.entries.map (·.2)
    recovery := g.recovers.map (·.2.2)
    directLr := lr.1
    otherLr := lr.2.1
    growing := lr.2.2
    rules := rules.map (fun r => (r.name, r))
    expandable := ((rules.filter expandable).map (·.name)).filter
      (fun n => !lr.1.contains n && !lr.2.1.contains n) }

def refName : Expr → String
  | .ref _ n _ => n
  | _ => ""

-- M.findWithDefault [] n (ctxCallers ctx)
def callers (ctx : Ctx) (n : String) : List Site := ctx.refSites.filter (fun s => refName s.expr == n)

-- expandCall
def expandCall (ctx : Ctx) (n : String) (args : List (Loc × String)) : Option (List (List Item)) :=
  match findLast ctx.rules n with
  | none => none
  | some r =>
    if ctx.expandable.contains n then
      match paramMap r args with
      | none => none
      | some pm => r.alts.mapM (fun a => substItems pm a.items)
    else none

def unfold (ctx : Ctx) (l : Loc) : Expr → Option (List (List Item))
  | .ref _ n args => expandCall ctx n args
  | .group alts => some alts
  | .plus x => some [[(l, none, x), (l, none, .star x)]]
  | .star x => some [[(l, none, x), (l, none, .star x)], []]
  | .opt x => some [[(l, none, x)], []]
  | .capture x => some [[(l, none, x)]]
  | .discard x => some [[(l, none, x)]]
  | .label _ x _ => some [[(l, none, x)]]
  | _ => none

-- expansions
def expansions (ctx : Ctx) (depth : Nat) (matched a : List Item) : List (List Item) :=
  let m := commonPrefix matched a
  match a.drop m with
  | (l, _, e) :: rest =>
    if m < matched.length ∧ depth > 0 then
      match unfold ctx l e with
      | some alts =>
        let xs := alts.flatMap (fun alt => expansions ctx (depth - 1) matched (a.take m ++ alt ++ rest))
        if xs.length > maxExpansions then [a] else xs
      | none => [a]
    else [a]
  | [] => [a]
termination_by depth
decreasing_by omega

/-! ## Known prefixes (ADR 0038) -/

def literalsOnly : Expr → Option (List String)
  | .lit t _ => some [t]
  | _ => none

-- sequence of a list of lists: the cartesian product.
def sequenceL : List (List String) → List (List String)
  | [] => [[]]
  | xs :: rest => xs.flatMap (fun x => (sequenceL rest).map (x :: ·))

def sequenceLiterals (is : List Item) : Option (List String) :=
  (is.mapM (fun i => literalsOnly (itemExpr i))).map (fun ls => (sequenceL ls).map String.join)

def literals (ctx : Ctx) : Expr → Option (List String)
  | .lit t _ => some [t]
  | .capture x => literals ctx x
  | .label _ x _ => literals ctx x
  | .discard x => literals ctx x
  | .ref _ n [] => match findLast ctx.rules n with
    | some r => if r.alts.isEmpty then none
      else (r.alts.mapM (fun a => sequenceLiterals a.items)).map List.flatten
    | none => none
  | _ => none

def knownGo (ctx : Ctx) : List Item → List (List Char)
  | [] => [[]]
  | i :: rest => match literals ctx (itemExpr i) with
    | some ts => (ts.flatMap (fun t =>
        (if t.length ≥ maxKnown then [[]] else knownGo ctx rest).map
          (fun s => (t.toList ++ s).take maxKnown))).take 16
    | none => [[]]

def knownStrings (ctx : Ctx) (items : List Item) : List (List Char) :=
  (knownGo ctx items).filter (fun t => !t.isEmpty)

inductive Sim where
  | fail
  | ok (t : List Char)
  | unknown
  deriving DecidableEq, Repr

def capSim (rs : List Sim) : List Sim :=
  let rs' := rs.foldr (fun r acc => if acc.contains r then acc else r :: acc) []
  if rs'.length > 16 then [.unknown] else rs'

def isOk : Sim → Bool
  | .ok _ => true
  | _ => false

def inClass (rs : List (HChar × HChar)) (c : Char) : Bool :=
  rs.any (fun p => decide (p.1.val ≤ c.toNat) && decide (c.toNat ≤ p.2.val))

def one (p : Char → Bool) (t : List Char) : List Sim :=
  match t with
  | [] => [.unknown]
  | c :: rest => if p c then [.ok rest] else [.fail]

set_option linter.unusedVariables false in
mutual
def simExpr (ctx : Ctx) (d : Nat) (t : List Char) : Expr → List Sim
  | .lit l _ =>
    let l := l.toList
    let n := min l.length t.length
    if l.isEmpty then [.ok t]
    else if l.take n != t.take n then [.fail]
    else if l.length ≤ t.length then [.ok (t.drop l.length)]
    else [.unknown]
  | .cls rs _ => one (inClass rs) t
  | .any => one (fun _ => true) t
  | .ref _ n args =>
    if h : d > 0 then
      match expandCall ctx n args with
      | some alts => choice ctx (d - 1) t alts
      | none => [.unknown]
    else [.unknown]
  | .group alts => choice ctx d t alts
  | .star x => star ctx d x t
  | .plus x => capSim ((simExpr ctx d t x).flatMap (fun r => match r with
      | .ok t' => star ctx d x t'
      | r => [r]))
  | .opt x => capSim ((simExpr ctx d t x).flatMap (fun r => match r with
      | .fail => [.ok t]
      | r => [r]))
  | .and x =>
    let rs := simExpr ctx d t x
    if rs.all (· == .fail) then [.fail] else if rs.all isOk then [.ok t] else [.unknown]
  | .not x =>
    let rs := simExpr ctx d t x
    if rs.all (· == .fail) then [.ok t] else if rs.all isOk then [.fail] else [.unknown]
  | .capture x => simExpr ctx d t x
  | .label _ x _ => simExpr ctx d t x
  | .discard x => simExpr ctx d t x
  | .pred b c => match constantPred b c with
    | some true => [.ok t]
    | some false => [.fail]
    | none => [.unknown]
  | .template .. => [.unknown]
termination_by e => (d, sizeOf e, t.length, 0)

-- simSeq ctx d t (map itemExpr items)
def simSeq (ctx : Ctx) (d : Nat) (t : List Char) : List Item → List Sim
  | [] => [.ok t]
  | (_, _, e) :: es => capSim ((simExpr ctx d t e).flatMap (fun r => match r with
      | .ok t' => simSeq ctx d t' es
      | r => [r]))
termination_by es => (d, sizeOf es, t.length, 0)

def choice (ctx : Ctx) (d : Nat) (t : List Char) : List (List Item) → List Sim
  | [] => [.fail]
  | alt :: rest =>
    let rs := simSeq ctx d t alt
    if rs.all (· == .fail) then choice ctx d t rest
    else if !rs.contains .fail then rs
    else capSim (rs.filter (· != .fail) ++ choice ctx d t rest)
termination_by alts => (d, sizeOf alts, t.length, 0)

def star (ctx : Ctx) (d : Nat) (x : Expr) (t' : List Char) : List Sim :=
  capSim ((simExpr ctx d t' x).flatMap (fun r => match r with
    | .fail => [.ok t']
    | .ok t'' => if h : t''.length < t'.length then star ctx d x t'' else [.ok t'']
    | .unknown => [.unknown]))
termination_by (d, sizeOf x, t'.length, 1)
end

def knownFails (ctx : Ctx) (matched rest : List Item) : Bool :=
  match knownStrings ctx matched with
  | [] => false
  | ss => ss.all (fun t => (simSeq ctx expandDepth t rest).all (· == .fail))

/-! ## The check -/

inductive Verdict where
  | safe
  | mayReject (why : String)
  | unchecked (why : String)
  deriving DecidableEq, Repr

def andAlso : Verdict → Verdict → Verdict
  | .safe, v => v
  | v, _ => v

inductive Mode where
  | failed
  | succeeded
  deriving DecidableEq, Repr

-- The key of the visited set: the rule, the frames, the mode, the next
-- characters, and the matched items.
abbrev Key := String × List (Nat × Nat) × Mode × CharSet × String

abbrev Visited := List Key

abbrev M := Visited → Option (Verdict × Visited)

def preKey (lifts : Nat) (pre : List Item) : String :=
  reprStr (lifts, pre.map (fun i => plainExpr (itemExpr i)))

def visit (key : Key) (act : M) : M := fun s =>
  if s.contains key then some (.safe, s) else act (key :: s)

def ret (v : Verdict) : M := fun s => some (v, s)

def allOf : List M → M
  | [] => ret .safe
  | a :: as => fun s => match a s with
    | none => none
    | some (v, s') => if v = .safe then allOf as s' else some (v, s')

def showLoc (l : Loc) : String := toString l.line ++ ":" ++ toString l.col

def beforeItems (ctx : Ctx) (prefix' : List Item) (k : CharSet) : CharSet :=
  let a := seqAbs ctx.pass prefix'
  a.consume.union (a.empty.intersect k)

-- The recursive functions of one step: failed and succeeded.
structure Rec where
  failed : String → List Frame → List Item × Nat → CharSet → M
  succeeded : String → List Frame → CharSet → M

def callersOf (ctx : Ctx) (rule : String) : List Site :=
  (callers ctx rule).filter fun s => !(match s.frames with
    | [.seq _ 0, .alts _ i true] => s.rule == rule && ctx.directLr.contains rule && ctx.growing rule i
    | _ => false)

-- lift of ruleFailed
def lift (ctx : Ctx) (rule : String) (pre : List Item) (lifts : Nat) (k : CharSet) (s : Site) :
    (List Item × Nat) × CharSet :=
  let fallback := (([], 0), beforeItems ctx pre k)
  match s.expr with
  | .ref _ _ args =>
    if lifts < maxLifts then
      match (findLast ctx.rules rule).bind (fun r => (paramMap r args).bind (fun pm => substItems pm pre)) with
      | some pre' =>
        if (pre'.flatMap (fun i => exprCodes (itemExpr i))).all (fun c => c.length ≤ maxCode') then
          ((pre', lifts + 1), k)
        else fallback
      | none => fallback
    else fallback
  | _ => fallback

def ruleFailed (ctx : Ctx) (R : Rec) (rule : String) (pre : List Item) (lifts : Nat) (k : CharSet) : M :=
  if ctx.recovery.contains rule then ret .safe
  else allOf ((callersOf ctx rule).map fun s =>
    let p := lift ctx rule pre lifts k s
    R.failed s.rule s.frames p.1 p.2)

def ruleSucceeded (ctx : Ctx) (R : Rec) (rule : String) (k : CharSet) : M :=
  if ctx.recovery.contains rule then ret .safe
  else if ctx.entries.contains rule && k.meets endOfInput then
    ret (.mayReject ("the input can end after the rule " ++ rule ++ ", which is an entry"))
  else allOf ((callersOf ctx rule).map fun s => R.succeeded s.rule s.frames k)

-- The body of failed, after the visit, with pre and k replaced as in its where clause.
def failedBody (ctx : Ctx) (R : Rec) (rule : String) (fs : List Frame) (pre : List Item) (lifts : Nat)
    (k : CharSet) : M :=
  let kStart := beforeItems ctx pre k
  match fs with
  | .seq items j :: .alts alts i body :: rest =>
    let matched := items.take j ++ pre
    let kAt := fun m => beforeItems ctx (matched.drop m) k
    let growingAlt := body && ctx.directLr.contains rule && ctx.growing rule i
    let later := ((indexed 0 alts).drop (i + 1)).filter (fun p => !growingAlt || ctx.growing rule p.1)
    let compareWith := fun (al : Loc) (a' : List Item) =>
      let m := commonPrefix matched a'
      let rest' := a'.drop m
      if (possible (seqAbs ctx.pass rest')).meets (kAt m) && !knownFails ctx (matched.drop m) rest' then
        Verdict.mayReject ("the alternative at " ++ showLoc al ++ " can match")
      else .safe
    let laterCheck := fun (p : Nat × Loc × List Item) =>
      if commonPrefix items p.2.2 > j then Verdict.safe
      else ((expansions ctx expandDepth matched p.2.2).map (compareWith p.2.1)).foldr andAlso .safe
    if body && ctx.otherLr.contains rule && ctx.growing rule i then
      ret (.unchecked ("it is in a growing alternative of " ++ rule ++
        ", which takes part in indirect or hidden left recursion"))
    else match (later.map laterCheck).foldr andAlso .safe with
      | .safe => if growingAlt then R.succeeded rule [] (kAt 1) else R.failed rule rest (matched, lifts) k
      | v => ret v
  | .star _ _ :: rest => R.succeeded rule rest kStart
  | .plus _ _ :: rest => allOf [R.failed rule rest (pre, lifts) k, R.succeeded rule rest kStart]
  | .opt :: rest => R.succeeded rule rest kStart
  | .and _ :: _ => ret .safe
  | .not _ :: _ => ret .safe
  | .label :: rest => R.failed rule rest (pre, lifts) k
  | .capture :: rest => R.failed rule rest (pre, lifts) k
  | [] => ruleFailed ctx R rule pre lifts k
  | _ => ret .safe

def succeededBody (ctx : Ctx) (R : Rec) (rule : String) (fs : List Frame) (k : CharSet) : M :=
  let again := fun (x : Expr) (l : Loc) (rest : List Frame) =>
    if (possible (exprAbs ctx.pass x)).meets k then
      ret (.mayReject ("the repetition at " ++ showLoc l ++ " can continue"))
    else R.succeeded rule rest k
  match fs with
  | .seq items j :: .alts as' i body :: rest =>
    let after := items.drop (j + 1)
    let a := seqAbs ctx.pass after
    let growingAlt := body && ctx.directLr.contains rule && ctx.growing rule i
    let ended := fun (k' : CharSet) =>
      if growingAlt then
        allOf (R.succeeded rule [] k' ::
          ((indexed 0 as').filter (fun p => ctx.growing rule p.1)).map
            (fun p => R.succeeded rule [.seq p.2.2 0, .alts as' p.1 true] k'))
      else R.succeeded rule rest k'
    if body && ctx.otherLr.contains rule && ctx.growing rule i then
      ret (.unchecked ("it reaches a growing alternative of " ++ rule ++
        ", which takes part in indirect or hidden left recursion"))
    else match after with
      | next :: _ =>
        if a.consume.meets k then ret (.mayReject ("the parse can continue at " ++ showLoc (itemLoc next)))
        else allOf ([R.failed rule (.seq items (j + 1) :: .alts as' i body :: rest) ([], 0) k] ++
          ((List.range' (j + 2) (items.length - (j + 2))).map
            (fun m => R.failed rule (.seq items m :: .alts as' i body :: rest) ([], 0) everything)) ++
          (if a.empty.meets k then [ended (a.empty.intersect k)] else []))
      | [] => allOf ((if a.empty.meets k then [ended (a.empty.intersect k)] else []))
  | .star x l :: rest => again x l rest
  | .plus x l :: rest => again x l rest
  | .opt :: rest => R.succeeded rule rest k
  | .and l :: _ => ret (.mayReject ("the lookahead at " ++ showLoc l ++ " can match"))
  | .not l :: _ => ret (.mayReject ("the lookahead at " ++ showLoc l ++ " can match"))
  | .label :: rest => R.succeeded rule rest k
  | .capture :: rest => R.succeeded rule rest k
  | [] => ruleSucceeded ctx R rule k
  | _ => ret .safe

-- The where clause of failed: a long prefix is replaced by its first characters.
def truncate (ctx : Ctx) (pre0 : List Item) (k0 : CharSet) : List Item × CharSet :=
  if pre0.length > maxPrefix then ([], beforeItems ctx pre0 k0) else (pre0, k0)

def failedKey (rule : String) (fs : List Frame) (pre : List Item) (lifts : Nat) (k : CharSet) : Key :=
  (rule, fs.map frameKey, .failed, k, preKey lifts pre)

def succeededKey (rule : String) (fs : List Frame) (k : CharSet) : Key :=
  (rule, fs.map frameKey, .succeeded, k, preKey 0 [])

def step (ctx : Ctx) (R : Rec) : Rec :=
  { failed := fun rule fs p k0 =>
      let t := truncate ctx p.1 k0
      visit (failedKey rule fs t.1 p.2 t.2) (failedBody ctx R rule fs t.1 p.2 t.2)
    succeeded := fun rule fs k =>
      visit (succeededKey rule fs k) (succeededBody ctx R rule fs k) }

def run (ctx : Ctx) : Nat → Rec
  | 0 => ⟨fun _ _ _ _ _ => none, fun _ _ _ _ => none⟩
  | n + 1 => step ctx (run ctx n)

-- The next characters where the label's expression x fails.
def startSet (ctx : Ctx) (x : Expr) : CharSet := everything.minus (exprAbs ctx.pass x).sure

-- verdictOf, with a fuel.
def verdictFuel (ctx : Ctx) (n : Nat) (rule : String) (fs : List Frame) (x : Expr) : Option Verdict :=
  ((run ctx n).failed rule fs ([], 0) (startSet ctx x) []).map (·.1)

def verdictMessage (name : String) : Verdict → Option String
  | .safe => none
  | .mayReject why => some ("the label " ++ name ++ " may reject valid input: where it fails, " ++ why)
  | .unchecked why => some ("the label " ++ name ++ " cannot be checked: " ++ why)

-- labelWarnings, for a function that gives the verdict on a label.
def labelWarningsWith (verdict : Ctx → String → List Frame → Expr → Verdict) (g : Grammar) :
    List Diagnostic :=
  let safe := g.safe.map (·.2)
  let ctx := context (unlabelGrammar g)
  (g.rules.flatMap sites).filterMap fun s =>
    match s.expr with
    | .label _ x name =>
      if safe.contains name then none
      else (verdictMessage name (verdict ctx s.rule (unlabelFrames s.frames) (unlabelExpr x))).map
        (Diagnostic.mk s.loc)
    | _ => none

-- The warning about the label at a site, if any; none when the verdict function gives none.
def warningAt (safe : List String) (verdict : String → List Frame → Expr → Option Verdict) (s : Site) :
    Option (Option Diagnostic) :=
  match s.expr with
  | .label _ x name =>
    if safe.contains name then some none
    else (verdict s.rule (unlabelFrames s.frames) (unlabelExpr x)).map fun v =>
      (verdictMessage name v).map (Diagnostic.mk s.loc)
  | _ => some none

-- labelWarnings with the fuel n; none when the fuel does not give a verdict on a label.
def labelWarningsFuel (n : Nat) (g : Grammar) : Option (List Diagnostic) :=
  let ctx := context (unlabelGrammar g)
  ((g.rules.flatMap sites).mapM (warningAt (g.safe.map (·.2)) (verdictFuel ctx n))).map (·.filterMap id)

/-! ## Removing labels: stripLabels -/

mutual
def stripExpr : Expr → Expr
  | .label _ x _ => stripExpr x
  | .discard x => .discard (stripExpr x)
  | .group alts => .group (stripAlts alts)
  | .star x => .star (stripExpr x)
  | .plus x => .plus (stripExpr x)
  | .opt x => .opt (stripExpr x)
  | .and x => .and (stripExpr x)
  | .not x => .not (stripExpr x)
  | .capture x => .capture (stripExpr x)
  | e => e
termination_by e => sizeOf e

def stripItems : List Item → List Item
  | [] => []
  | (l, b, e) :: is => (l, b, stripExpr e) :: stripItems is
termination_by is => sizeOf is

def stripAlts : List (List Item) → List (List Item)
  | [] => []
  | a :: as => stripItems a :: stripAlts as
termination_by as => sizeOf as
end

def recoveryGo : List String → List (Loc × String) → List (Loc × String)
  | _, [] => []
  | seen, r :: rs => if seen.contains r.2 then recoveryGo seen rs else r :: recoveryGo (r.2 :: seen) rs

def recoveryEntries (g : Grammar) : List (Loc × String) :=
  recoveryGo (startName g :: g.entries.map (·.2)) (g.recovers.map (·.2))

def stripLabels (g : Grammar) : Grammar :=
  { g with
    recovers := []
    safe := []
    messages := []
    entries := g.entries ++ recoveryEntries g
    rules := g.rules.map (fun r => { r with alts := r.alts.map (fun a => { a with items := stripItems a.items }) }) }

def stripLabelsAs (m : String) (g : Grammar) : Grammar :=
  { stripLabels g with module := (g.module.1, m) }

end PegHs.LabelCheck
