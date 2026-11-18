import Lean
import AssembleChars

/-!
The Haskell library functions that TranslateHaskell.hs maps to Lean.

TranslateHaskell.hs translates the syntax of a Haskell module and replaces
each library function (by its module, name and the type it is used at) with
one definition of this file. That the two compute the same value is an
evaluation rule of the translation (ADR 0097: "翻訳器と Haskell の評価規則に
置いた仮定を記録する"). The rules, numbered as in verification/README.md:

- H1 Types. `Int` is Lean's `Int`: the translated code does not reach the
  bounds of a 64-bit Haskell `Int`. `Char` is `HsChar`, a code point below
  0x110000. `Text` is `String`: a `Text` holds Unicode scalar values, and
  so does a `String`. `[a]`, `Maybe a`, tuples, `Bool` and `()` are `List`,
  `Option`, products, `Bool` and `Unit`.
- H2 Lists, `Maybe`, tuples, booleans and integers: each function below
  computes what the base function of the same name computes on finite
  values. `sortOn` is a stable sort by a key (any stable sort gives the same
  list); `Data.Char.isSpace`, `isAlpha` and `isAlphaNum` are the tables of
  GHC 9.10.3 (check-translate-labels.sh rebuilds `spaceRanges`;
  check-assemble-predicates.sh rebuilds the AssembleChars tables).
- H3 `Data.Text`: each function computes what text-2.1 computes on the
  scalar values of the text.
- H4 `Data.Map` and `Data.Set`: a map is a list of pairs with distinct keys
  and a set a list of distinct elements. Lookup, membership, insertion and
  the construction from a list behave as containers' do; equality is
  extensional, as containers' `Eq` is; `S.toList` sorts.
- H5 `==` on a type that derives `Eq` is Lean's derived `BEq`: both compare
  constructors and fields structurally.
- H6 Evaluation. The Lean definitions are total; Haskell's lazy evaluation
  of a terminating expression gives the value the Lean term denotes. A
  pattern match that Haskell would fail on gives `hsUndefined` (the default
  value) instead of an error. A function translated with fuel gives the
  Haskell value at every fuel large enough when the Haskell evaluation
  terminates.
-/

/-! ## Characters -/

/-- A Haskell `Char`: a code point. -/
structure HsChar where
  val : Nat
  isLt : val < 0x110000
  deriving DecidableEq, Repr

instance : Inhabited HsChar := ⟨⟨0, by decide⟩⟩

def HsChar.ofNat (n : Nat) : HsChar :=
  if h : n < 0x110000 then ⟨n, h⟩ else ⟨0, by decide⟩

theorem char_toNat_lt (c : Char) : c.toNat < 0x110000 := by
  have h := c.valid
  simp [UInt32.isValidChar, Nat.isValidChar] at h
  omega

def HsChar.ofChar (c : Char) : HsChar := ⟨c.toNat, char_toNat_lt c⟩

def HsChar.le (a b : HsChar) : Bool := decide (a.val ≤ b.val)

def HsChar.fromEnum (c : HsChar) : Int := Int.ofNat c.val

-- Data.Char.isSpace of GHC 9.10.3, as ranges of code points.
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

def inRangesNat (rs : List (Nat × Nat)) (n : Nat) : Bool :=
  rs.any (fun r => decide (r.1 ≤ n ∧ n ≤ r.2))

def isSpaceChar (c : Char) : Bool := inRangesNat spaceRanges c.toNat

-- Data.Char.isAlpha and isAlphaNum: the tables of AssembleChars, which
-- check-assemble-predicates.sh rebuilds from GHC 9.10.3.
def HsChar.isAlpha (c : HsChar) : Bool := inRangesNat PegHs.AssembleChars.alphaRanges c.val
def HsChar.isAlphaNum (c : HsChar) : Bool := inRangesNat PegHs.AssembleChars.alphaNumRanges c.val

/-! ## Integers -/

namespace HsInt
def lt (a b : Int) : Bool := decide (a < b)
def le (a b : Int) : Bool := decide (a ≤ b)
def gt (a b : Int) : Bool := decide (a > b)
def ge (a b : Int) : Bool := decide (a ≥ b)
def add (a b : Int) : Int := a + b
def sub (a b : Int) : Int := a - b
def neg (a : Int) : Int := -a
def max (a b : Int) : Int := if a ≤ b then b else a
def min (a b : Int) : Int := if a ≤ b then a else b
def «show» (a : Int) : List HsChar := (toString a).toList.map HsChar.ofChar
end HsInt

/-! ## Functions of base -/

def hsUndefined {α : Type} [Inhabited α] : α := default

namespace HsBase
def eq {α : Type} [BEq α] (a b : α) : Bool := a == b
def ne {α : Type} [BEq α] (a b : α) : Bool := !(a == b)
def and (a b : Bool) : Bool := a && b
def or (a b : Bool) : Bool := a || b
def not (a : Bool) : Bool := !a
def comp {α β γ : Type} (f : β → γ) (g : α → β) : α → γ := fun x => f (g x)
def apply {α β : Type} (f : α → β) (x : α) : β := f x
def const {α β : Type} (a : α) (_ : β) : α := a
def flip {α β γ : Type} (f : α → β → γ) (b : β) (a : α) : γ := f a b
def id {α : Type} (a : α) : α := a
def uncurry {α β γ : Type} (f : α → β → γ) (p : α × β) : γ := f p.1 p.2
def maybe {α β : Type} (d : β) (f : α → β) : Option α → β
  | none => d
  | some a => f a
def seq {α β : Type} (_ : α) (b : β) : β := b
end HsBase

namespace HsList
def append {α : Type} (xs ys : List α) : List α := xs ++ ys
def take {α : Type} (n : Int) (xs : List α) : List α := xs.take n.toNat
def drop {α : Type} (n : Int) (xs : List α) : List α := xs.drop n.toNat
def length {α : Type} (xs : List α) : Int := Int.ofNat xs.length
def null {α : Type} (xs : List α) : Bool := xs.isEmpty
def elem {α : Type} [BEq α] (x : α) (xs : List α) : Bool := xs.any (· == x)
def notElem {α : Type} [BEq α] (x : α) (xs : List α) : Bool := !(xs.any (· == x))
def any {α : Type} (p : α → Bool) (xs : List α) : Bool := xs.any p
def all {α : Type} (p : α → Bool) (xs : List α) : Bool := xs.all p
def and (xs : List Bool) : Bool := xs.all (·)
def concat {α : Type} (xss : List (List α)) : List α := xss.flatten
def concatMap {α β : Type} (f : α → List β) (xs : List α) : List β := xs.flatMap f
def foldr {α β : Type} (f : α → β → β) (z : β) (xs : List α) : β := xs.foldr f z
def catMaybes {α : Type} (xs : List (Option α)) : List α := xs.filterMap (·)
-- A stable insertion sort by an integer key.
def insertOn {α : Type} (key : α → Int) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if key x ≤ key y then x :: y :: ys else y :: insertOn key x ys
def sortOn {α : Type} (key : α → Int) : List α → List α
  | [] => []
  | x :: xs => insertOn key x (sortOn key xs)
-- sequence in the list monad: every choice of one element of each list.
def sequence {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap (fun x => (sequence xss).map (x :: ·))
-- zip [n ..] xs
def zipFrom {α : Type} (n : Int) : List α → List (Int × α)
  | [] => []
  | x :: xs => (n, x) :: zipFrom (n + 1) xs
-- [a .. b]
def enumFromTo (a b : Int) : List Int :=
  (List.range (b + 1 - a).toNat).map (fun i => a + Int.ofNat i)
end HsList

-- Lean's termination checker attaches membership to the elements that these
-- functions pass to their function argument (as for List.map in core).
@[wf_preprocess] theorem HsList.concatMap_wfParam {α β : Type} {f : α → List β} {xs : List α} :
    HsList.concatMap f (wfParam xs) = HsList.concatMap f xs.attach.unattach := by
  simp [wfParam]
@[wf_preprocess] theorem HsList.concatMap_unattach {α β : Type} {P : α → Prop} {xs : List (Subtype P)} {f : α → List β} :
    HsList.concatMap f xs.unattach = HsList.concatMap (fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x)) xs := by
  simp [HsList.concatMap, wfParam]
@[wf_preprocess] theorem HsList.any_wfParam {α : Type} {p : α → Bool} {xs : List α} :
    HsList.any p (wfParam xs) = HsList.any p xs.attach.unattach := by
  simp [wfParam]
@[wf_preprocess] theorem HsList.any_unattach {α : Type} {P : α → Prop} {xs : List (Subtype P)} {p : α → Bool} :
    HsList.any p xs.unattach = HsList.any (fun ⟨x, h⟩ =>
      binderNameHint x p <| binderNameHint h () <| p (wfParam x)) xs := by
  simp [HsList.any, wfParam]
@[wf_preprocess] theorem HsList.all_wfParam {α : Type} {p : α → Bool} {xs : List α} :
    HsList.all p (wfParam xs) = HsList.all p xs.attach.unattach := by
  simp [wfParam]
@[wf_preprocess] theorem HsList.all_unattach {α : Type} {P : α → Prop} {xs : List (Subtype P)} {p : α → Bool} :
    HsList.all p xs.unattach = HsList.all (fun ⟨x, h⟩ =>
      binderNameHint x p <| binderNameHint h () <| p (wfParam x)) xs := by
  simp [HsList.all, wfParam]
@[wf_preprocess] theorem HsList.foldr_wfParam {α β : Type} {f : α → β → β} {z : β} {xs : List α} :
    HsList.foldr f z (wfParam xs) = HsList.foldr f z xs.attach.unattach := by
  simp [wfParam]
@[wf_preprocess] theorem HsList.foldr_unattach {α β : Type} {P : α → Prop} {xs : List (Subtype P)} {f : α → β → β} {z : β} :
    HsList.foldr f z xs.unattach = HsList.foldr (fun ⟨x, h⟩ s =>
      binderNameHint x f <| binderNameHint s (f x) <| binderNameHint h () <| f (wfParam x) s) z xs := by
  simp [HsList.foldr, wfParam]

namespace HsMaybe
def fmap {α β : Type} (f : α → β) : Option α → Option β
  | none => none
  | some a => some (f a)
def ap {α β : Type} : Option (α → β) → Option α → Option β
  | some f, some a => some (f a)
  | _, _ => none
def bind {α β : Type} : Option α → (α → Option β) → Option β
  | none, _ => none
  | some a, k => k a
def pure {α : Type} (a : α) : Option α := some a
def mapM {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => match f x with
    | none => none
    | some y => match mapM f xs with
      | none => none
      | some ys => some (y :: ys)
end HsMaybe

/-! ## Data.Text -/

namespace HsText
def uncons (s : String) : Option (HsChar × String) :=
  match s.toList with
  | [] => none
  | c :: cs => some (HsChar.ofChar c, String.ofList cs)
def null (s : String) : Bool := s.toList.isEmpty
def append (a b : String) : String := a ++ b
def length (s : String) : Int := Int.ofNat s.toList.length
def take (n : Int) (s : String) : String := String.ofList (s.toList.take n.toNat)
def drop (n : Int) (s : String) : String := String.ofList (s.toList.drop n.toNat)
-- T.pack replaces a surrogate code point with U+FFFD.
def toChar (c : HsChar) : Char :=
  if c.val.isValidChar then Char.ofNat c.val else '\uFFFD'
def pack (cs : List HsChar) : String := String.ofList (cs.map toChar)
def all (p : HsChar → Bool) (s : String) : Bool := s.toList.all (fun c => p (HsChar.ofChar c))
def span (p : HsChar → Bool) (s : String) : String × String :=
  (String.ofList (s.toList.takeWhile (fun c => p (HsChar.ofChar c))),
   String.ofList (s.toList.dropWhile (fun c => p (HsChar.ofChar c))))
def «break» (p : HsChar → Bool) (s : String) : String × String :=
  span (fun c => !p c) s
def strip (s : String) : String :=
  String.ofList (((s.toList.dropWhile isSpaceChar).reverse.dropWhile isSpaceChar).reverse)
def splitList (p : Char → Bool) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if p c then [] :: splitList p cs
    else match splitList p cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]
def split (p : HsChar → Bool) (s : String) : List String :=
  (splitList (fun c => p (HsChar.ofChar c)) s.toList).map String.ofList
def isInfixList (needle hay : List Char) : Bool :=
  match hay with
  | [] => needle.isEmpty
  | _ :: rest => needle.isPrefixOf hay || isInfixList needle rest
def isInfixOf (needle hay : String) : Bool := isInfixList needle.toList hay.toList
def concat (ts : List String) : String := String.join ts
end HsText

/-! ## Data.Map and Data.Set -/

/-- A map: pairs with distinct keys, in the order of their insertion. -/
structure HsMap (κ ν : Type) where
  pairs : List (κ × ν)
  deriving Inhabited

/-- A set: distinct elements, in the order of their insertion. -/
structure HsSet (α : Type) where
  elems : List α
  deriving Inhabited

namespace HsMap
def lookup {κ ν : Type} [BEq κ] (k : κ) (m : HsMap κ ν) : Option ν :=
  (m.pairs.find? (·.1 == k)).map (·.2)
def member {κ ν : Type} [BEq κ] (k : κ) (m : HsMap κ ν) : Bool := m.pairs.any (·.1 == k)
def insertWith {κ ν : Type} [BEq κ] (f : ν → ν → ν) (k : κ) (v : ν) (m : HsMap κ ν) : HsMap κ ν :=
  if member k m then ⟨m.pairs.map (fun p => if p.1 == k then (k, f v p.2) else p)⟩ else ⟨m.pairs ++ [(k, v)]⟩
def insert {κ ν : Type} [BEq κ] (k : κ) (v : ν) (m : HsMap κ ν) : HsMap κ ν :=
  insertWith (fun new _ => new) k v m
def fromList {κ ν : Type} [BEq κ] (xs : List (κ × ν)) : HsMap κ ν :=
  xs.foldl (fun m p => insert p.1 p.2 m) ⟨[]⟩
def fromListWith {κ ν : Type} [BEq κ] (f : ν → ν → ν) (xs : List (κ × ν)) : HsMap κ ν :=
  xs.foldl (fun m p => insertWith f p.1 p.2 m) ⟨[]⟩
def findWithDefault {κ ν : Type} [BEq κ] (d : ν) (k : κ) (m : HsMap κ ν) : ν :=
  (lookup k m).getD d
def keysSet {κ ν : Type} (m : HsMap κ ν) : HsSet κ := ⟨m.pairs.map (·.1)⟩
-- Extensional equality, as containers' Eq.
def beq {κ ν : Type} [BEq κ] [BEq ν] (a b : HsMap κ ν) : Bool :=
  a.pairs.all (fun p => lookup p.1 b == some p.2) && b.pairs.all (fun p => member p.1 a)
instance {κ ν : Type} [BEq κ] [BEq ν] : BEq (HsMap κ ν) := ⟨beq⟩
end HsMap

namespace HsSet
def member {α : Type} [BEq α] (x : α) (s : HsSet α) : Bool := s.elems.any (· == x)
def insert {α : Type} [BEq α] (x : α) (s : HsSet α) : HsSet α := if member x s then s else ⟨s.elems ++ [x]⟩
def fromList {α : Type} [BEq α] (xs : List α) : HsSet α := xs.foldl (fun s x => insert x s) ⟨[]⟩
def union {α : Type} [BEq α] (a b : HsSet α) : HsSet α := b.elems.foldl (fun s x => insert x s) a
def difference {α : Type} [BEq α] (a b : HsSet α) : HsSet α := ⟨a.elems.filter (fun x => !member x b)⟩
def singleton {α : Type} (x : α) : HsSet α := ⟨[x]⟩
def empty {α : Type} : HsSet α := ⟨[]⟩
def insertSorted (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if compare x y == .lt then x :: y :: ys else y :: insertSorted x ys
-- S.toList: ascending order (Text's order is the order of code points).
def toList (s : HsSet String) : List String := s.elems.foldr insertSorted []
-- Extensional equality, as containers' Eq.
def beq {α : Type} [BEq α] (a b : HsSet α) : Bool := a.elems.all (member · b) && b.elems.all (member · a)
instance {α : Type} [BEq α] : BEq (HsSet α) := ⟨beq⟩
end HsSet

/-! ## Termination of translated recursion -/

open Lean in
/-- The closed arguments of the applications in a term. -/
partial def hsArgsOf (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isApp && !e.appArg!.hasLooseBVars then acc.push e.appArg! else acc
  match e with
  | .app f a => hsArgsOf a (hsArgsOf f acc)
  | .lam _ t b _ => hsArgsOf b (hsArgsOf t acc)
  | .forallE _ t b _ => hsArgsOf b (hsArgsOf t acc)
  | .mdata _ b => hsArgsOf b acc
  | .proj _ _ b => hsArgsOf b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- Facts for Lean's termination checker: for each hypothesis `h : a ∈ l`
(or attached element) with `l` a list, `sizeOf a < sizeOf l`; and for each
lemma `f_sizeOf : sizeOf (T.f r) < sizeOf r` named, its instances at the
local variables and at the record arguments of the field selections in the
goal. -/
elab "hs_sizes" " [" lemmas:ident,* "]" : tactic => withMainContext do
  let mut facts : Array Expr := #[]
  for h in (← getLCtx) do
    if h.isImplementationDetail then continue
    let mem? ← try some <$> mkAppM ``List.sizeOf_lt_of_mem #[h.toExpr] catch _ =>
      try some <$> (do
        let p ← mkAppM ``Subtype.property #[h.toExpr]
        mkAppM ``List.sizeOf_lt_of_mem #[p]) catch _ => pure none
    if let some pf := mem? then facts := facts.push pf
  -- Terms of the goal and the hypotheses: field lemmas at each of them.
  let goal ← instantiateMVars (← getMainTarget)
  let mut terms : Array Expr := #[]
  for h in (← getLCtx) do
    if h.isImplementationDetail then continue
    terms := terms.push h.toExpr
  terms := hsArgsOf goal terms
  for lem in lemmas.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo lem
    for t in terms do
      let pf? ← try some <$> mkAppM name #[t] catch _ => pure none
      if let some pf := pf? then facts := facts.push pf
  for pf in facts do
    let ty ← inferType pf
    liftMetaTactic fun g => do
      let g' ← g.assert `hsz ty pf
      let (_, g'') ← g'.intro1P
      return [g'']

/-! ## show compared for equality -/

-- Rule H7: `show` at a type other than Int is translated only where its
-- results are compared with each other (the key of a set). Haskell's derived
-- Show and Lean's derived Repr are both injective, so the comparisons agree.
def HsShow.viaRepr {α : Type} [Repr α] (x : α) : List HsChar :=
  (reprStr x).toList.map HsChar.ofChar

/-! ## Data.Graph (containers 0.7) -/

inductive HsSCC (α : Type) where
  | AcyclicSCC : α → HsSCC α
  | CyclicSCC : List α → HsSCC α
  deriving Inhabited

namespace HsGraph

inductive Tree where
  | node : Nat → List Tree → Tree

-- dfs: the preorder forest from the roots in order, skipping the visited
-- vertices. The fuel bounds the steps; fuelOf is more than dfs takes.
mutual
def dfsList (g : Array (List Nat)) : Nat → List Nat → List Nat → List Tree × List Nat
  | 0, _, visited => ([], visited)
  | _ + 1, [], visited => ([], visited)
  | fuel + 1, v :: vs, visited =>
    if visited.contains v then dfsList g fuel vs visited
    else
      let r := dfsNode g fuel v (v :: visited)
      let rs := dfsList g fuel vs r.2
      (r.1 :: rs.1, rs.2)
def dfsNode (g : Array (List Nat)) : Nat → Nat → List Nat → Tree × List Nat
  | 0, v, visited => (.node v [], visited)
  | fuel + 1, v, visited =>
    let r := dfsList g fuel (g.getD v []) visited
    (.node v r.1, r.2)
end

def fuelOf (g : Array (List Nat)) : Nat :=
  (g.size + 1) * (g.foldl (fun n es => n + es.length) 0 + g.size + 2)

def dfs (g : Array (List Nat)) (roots : List Nat) : List Tree :=
  (dfsList g (fuelOf g) roots []).1

-- postorderF: the children before their parent, the trees in order.
mutual
def postTree : Tree → List Nat → List Nat
  | .node v ts, acc => postForest ts (v :: acc)
def postForest : List Tree → List Nat → List Nat
  | [], acc => acc
  | t :: ts, acc => postTree t (postForest ts acc)
end

def postOrd (g : Array (List Nat)) : List Nat :=
  postForest (dfs g (List.range g.size)) []

-- transposeG: buildG of reverseE, with accumArray (flip (:)) [].
def transposeG (g : Array (List Nat)) : Array (List Nat) :=
  let edges := (List.range g.size).flatMap (fun v => (g.getD v []).map (fun w => (w, v)))
  edges.foldl (fun acc (e : Nat × Nat) => acc.modify e.1 (fun es => e.2 :: es)) (Array.replicate g.size [])

def scc (g : Array (List Nat)) : List Tree :=
  dfs g (postOrd (transposeG g)).reverse

-- dec (Node v ts) vs = vertex_fn v : foldr dec vs ts
mutual
def decTree {α : Type} (vf : Nat → α) : Tree → List α → List α
  | .node v ts, vs => vf v :: decForest vf ts vs
def decForest {α : Type} (vf : Nat → α) : List Tree → List α → List α
  | [], vs => vs
  | t :: ts, vs => decTree vf t (decForest vf ts vs)
end

-- graphFromEdges sorts the nodes by key, stably, and numbers them.
def insertOnKey {α : Type} (x : α × String × List String) : List (α × String × List String) → List (α × String × List String)
  | [] => [x]
  | y :: ys => if compare x.2.1 y.2.1 == .gt then y :: insertOnKey x ys else x :: y :: ys

def stronglyConnComp {α : Type} [Inhabited α] (edges0 : List (α × String × List String)) : List (HsSCC α) :=
  let nodes := edges0.foldr insertOnKey []
  let keyVertex (k : String) : Option Nat := nodes.findIdx? (fun e => e.2.1 == k)
  let g : Array (List Nat) := (nodes.map (fun e => e.2.2.filterMap keyVertex)).toArray
  let vf (v : Nat) : α := (nodes.getD v default).1
  let decode : Tree → HsSCC α := fun t => match t with
    | .node v [] => if (g.getD v []).contains v then .CyclicSCC [vf v] else .AcyclicSCC (vf v)
    | t => .CyclicSCC (decTree vf t [])
  (scc g).map decode

end HsGraph
