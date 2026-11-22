import Lean
import AssembleChars
import GeneralCategory
import UpperCase

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

Rules H7 and H8 are stated where their functions are defined. The rules
added for Peg.Grammar.Assemble:

- H9 Types. `Either a b` is `Except a b` (`Left` is `error`, `Right` is
  `ok`), `Integer` is `Int`, `Natural` is `Nat`, and `GeneralCategory` is
  `HsGeneralCategory`. `fromInteger` and `toInteger` between `Int` and
  `Integer` are the identity (rule H1: no `Int` overflows), and `maxBound`
  at `Int` is 2^63 - 1. The monad of `Either` binds as base's instance.
- H10 Data.Char: `isUpper` is the table of AssembleChars,
  `generalCategory` the table of GeneralCategory.lean (both rebuilt from
  GHC 9.10.3 by check-assemble-predicates.sh and
  check-translate-assemble.sh), `isSpace` the table `spaceRanges`;
  `isDigit`, `isHexDigit`, `isAscii`, `isAsciiUpper`, `digitToInt` and
  `chr` are base's definitions on code points. `toUpper` is the table of
  UpperCase.lean; `isSymbol` and `isPunctuation` test general categories.
  check-uppercase.sh compares every uppercase mapping and tests category
  boundaries and mutations against GHC.
- H11 `compare` on a type that derives `Ord` is Lean's derived `Ord`: both
  compare the constructors in their order, then the fields from left to
  right. `sortOn` with such a key is a stable sort by `compare`.
- H12 The functions of Data.Text in the second part of `HsText` (from
  `foldl'`) compute what text-2.1 computes on the scalar values of the text;
  `breakOn`, `breakOnEnd` and `splitOn` are given a nonempty needle.
- H13 `M.toList` and `M.elems` list a map in the ascending order of its
  keys, by the keys' `Ord`.
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

def HsChar.lt (a b : HsChar) : Bool := decide (a.val < b.val)
def HsChar.gt (a b : HsChar) : Bool := HsChar.lt b a

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

-- Rule H10: Data.Char's classifications.
def HsChar.isSpace (c : HsChar) : Bool := inRangesNat spaceRanges c.val
def HsChar.toUpper (c : HsChar) : HsChar :=
  ⟨PegHs.UpperCase.ofCode c.val, PegHs.UpperCase.ofCode_bounded c.val c.isLt⟩

def HsChar.isUpper (c : HsChar) : Bool := inRangesNat PegHs.AssembleChars.upperRanges c.val
def HsChar.generalCategory (c : HsChar) : HsGeneralCategory := HsGeneralCategory.ofCode c.val
def HsChar.isSymbol (c : HsChar) : Bool :=
  decide (c.generalCategory = .MathSymbol ∨ c.generalCategory = .CurrencySymbol ∨
    c.generalCategory = .ModifierSymbol ∨ c.generalCategory = .OtherSymbol)
def HsChar.isPunctuation (c : HsChar) : Bool :=
  decide (c.generalCategory = .ConnectorPunctuation ∨ c.generalCategory = .DashPunctuation ∨
    c.generalCategory = .OpenPunctuation ∨ c.generalCategory = .ClosePunctuation ∨
    c.generalCategory = .InitialQuote ∨ c.generalCategory = .FinalQuote ∨
    c.generalCategory = .OtherPunctuation)
def HsChar.isDigit (c : HsChar) : Bool := decide (48 ≤ c.val ∧ c.val ≤ 57)
def HsChar.isHexDigit (c : HsChar) : Bool :=
  c.isDigit || decide (65 ≤ c.val ∧ c.val ≤ 70) || decide (97 ≤ c.val ∧ c.val ≤ 102)
def HsChar.isAscii (c : HsChar) : Bool := decide (c.val < 128)
def HsChar.isAsciiUpper (c : HsChar) : Bool := decide (65 ≤ c.val ∧ c.val ≤ 90)
-- digitToInt fails on a character that is not a hexadecimal digit: 0 (H6).
def HsChar.digitToInt (c : HsChar) : Int :=
  if c.isDigit then Int.ofNat c.val - 48
  else if decide (97 ≤ c.val ∧ c.val ≤ 102) then Int.ofNat c.val - 87
  else if decide (65 ≤ c.val ∧ c.val ≤ 70) then Int.ofNat c.val - 55
  else 0
-- chr fails outside 0 .. 0x10FFFF: the character 0 (H6).
def HsChar.chr (n : Int) : HsChar := HsChar.ofNat n.toNat

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
def mul (a b : Int) : Int := a * b
-- div rounds towards negative infinity.
def div (a b : Int) : Int := Int.fdiv a b
def toInteger (a : Int) : Int := a
def fromInteger (a : Int) : Int := a
def maxBound : Int := 9223372036854775807
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
-- Consume only the head of a filtered infinite Integer enumeration. Running
-- out of evaluation fuel is undefined, not the source's empty-list branch.
def firstFrom {α β : Type} [Inhabited β] :
    Nat → Int → (Int → List α) → (α → β) → β
  | 0, _, _, _ => hsUndefined
  | fuel + 1, start, step, result =>
    match step start with
    | [] => firstFrom fuel (start + 1) step result
    | value :: _ => result value

theorem firstFrom_hit {α β : Type} [Inhabited β]
    (step : Int → List α) (result : α → β) (offset : Nat) :
    ∀ (start : Int) (fuel : Nat) (value : α) (tail : List α),
      offset < fuel →
      (∀ i : Nat, i < offset → step (start + i) = []) →
      step (start + offset) = value :: tail →
      firstFrom fuel start step result = result value := by
  induction offset with
  | zero =>
    intro start fuel value tail enough _ hit
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hit' : step start = value :: tail := by simpa using hit
      simp only [firstFrom, hit']
  | succ offset ih =>
    intro start fuel value tail enough earlier hit
    cases fuel with
    | zero => omega
    | succ fuel =>
      have empty := earlier 0 (by omega)
      simp only [Int.natCast_zero, Int.add_zero] at empty
      rw [firstFrom, empty]
      apply ih (start + 1) fuel value tail (by omega)
      · intro i before
        have h := earlier (i + 1) (by omega)
        simpa only [Int.natCast_add, Int.natCast_one, Int.add_assoc,
          Int.add_left_comm, Int.add_comm] using h
      · simpa only [Int.natCast_add, Int.natCast_one, Int.add_assoc,
          Int.add_left_comm, Int.add_comm] using hit
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
def reverse {α : Type} (xs : List α) : List α := xs.reverse
def lookup {α β : Type} [BEq α] (k : α) : List (α × β) → Option β
  | [] => none
  | (a, b) :: rest => if a == k then some b else lookup k rest
def span {α : Type} (p : α → Bool) (xs : List α) : List α × List α := (xs.takeWhile p, xs.dropWhile p)
def «break» {α : Type} (p : α → Bool) (xs : List α) : List α × List α := span (fun x => !p x) xs
theorem span_snd_length_le {α : Type} (p : α → Bool) (xs : List α) :
    (span p xs).2.length ≤ xs.length := by
  induction xs with
  | nil => simp [span]
  | cons x xs ih =>
    simp only [span, List.dropWhile_cons] at ih ⊢
    split <;> simp <;> omega
theorem span_cons_snd {α : Type} (p : α → Bool) (x : α) (xs : List α) (h : p x = true) :
    (span p (x :: xs)).2 = (span p xs).2 := by
  simp [span, h]
theorem span_eq_snd_length {α : Type} {p : α → Bool} {xs a b : List α} (h : span p xs = (a, b)) :
    b.length ≤ xs.length := by
  have := span_snd_length_le p xs
  rw [h] at this
  exact this
-- break that does not stop at the first element leaves at most the tail.
theorem break_cons_snd_length {α : Type} {p : α → Bool} {x : α} {xs a b : List α}
    (h : «break» p (x :: xs) = (a, b)) (hx : p x = false) : b.length ≤ xs.length := by
  have := span_snd_length_le (fun y => !p y) xs
  simp only [«break», span, List.dropWhile_cons, hx] at h this
  simp at h
  rw [← h.2]
  exact this
def foldl {α β : Type} (f : β → α → β) (z : β) (xs : List α) : β := xs.foldl f z
def sumInteger (xs : List Int) : Int := xs.foldl (· + ·) 0

theorem sumInteger_eq_sum (xs : List Int) : sumInteger xs = xs.sum := by
  have fold (values : List Int) (acc : Int) : values.foldl (· + ·) acc = acc + values.sum := by
    induction values generalizing acc with
    | nil => simp
    | cons x rest ih => simp [List.foldl, ih, Int.add_assoc]
  simpa [sumInteger] using fold xs 0

def pure {α : Type} (a : α) : List α := [a]
-- Rule H11: a stable insertion sort by a key with a derived Ord.
def insertOnOrd {α β : Type} [Ord β] (key : α → β) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if compare (key x) (key y) != .gt then x :: y :: ys else y :: insertOnOrd key x ys
def sortOnOrd {α β : Type} [Ord β] (key : α → β) : List α → List α
  | [] => []
  | x :: xs => insertOnOrd key x (sortOnOrd key xs)
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
def foldM {α β : Type} (f : β → α → Option β) (z : β) : List α → Option β
  | [] => some z
  | x :: xs => match f z x with
    | none => none
    | some z' => foldM f z' xs
def isNothing {α : Type} (value : Option α) : Bool := value.isNone

def isJust {α : Type} : Option α → Bool
  | some _ => true
  | none => false
-- bind with the equation of the bound value, for Lean's termination checker.
def bindAttach {α β : Type} : (o : Option α) → ((a : α) → o = some a → Option β) → Option β
  | none, _ => none
  | some a, f => f a rfl
@[wf_preprocess] theorem bind_eq_bindAttach {α β : Type} (o : Option α) (f : α → Option β) :
    bind o f = bindAttach o (fun a _ => f a) := by
  cases o <;> rfl
end HsMaybe

namespace HsEither
def pure {ε α : Type} (a : α) : Except ε α := .ok a
def bind {ε α β : Type} : Except ε α → (α → Except ε β) → Except ε β
  | .error e, _ => .error e
  | .ok a, k => k a
def fmap {ε α β : Type} (f : α → β) : Except ε α → Except ε β
  | .error e => .error e
  | .ok a => .ok (f a)
end HsEither

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
def head (text : String) : HsChar :=
  match text.toList with
  | [] => hsUndefined
  | c :: _ => HsChar.ofChar c

def pack (cs : List HsChar) : String := String.ofList (cs.map toChar)
def filter (predicate : HsChar → Bool) (text : String) : String := String.ofList (text.toList.filter (fun c => predicate (HsChar.ofChar c)))
def all (p : HsChar → Bool) (s : String) : Bool := s.toList.all (fun c => p (HsChar.ofChar c))
def span (p : HsChar → Bool) (s : String) : String × String :=
  (String.ofList (s.toList.takeWhile (fun c => p (HsChar.ofChar c))),
   String.ofList (s.toList.dropWhile (fun c => p (HsChar.ofChar c))))
def «break» (p : HsChar → Bool) (s : String) : String × String :=
  span (fun c => !p c) s

theorem span_append (p : HsChar → Bool) (s : String) :
    (span p s).1 ++ (span p s).2 = s := by
  simp only [span, ← String.ofList_append, List.takeWhile_append_dropWhile, String.ofList_toList]

theorem span_shrinks (p : HsChar → Bool) (s : String)
    (nonempty : null s = false) (first : p (head s) = true) :
    (span p s).2.toList.length < s.toList.length := by
  cases chars : s.toList with
  | nil => simp [null, chars] at nonempty
  | cons c cs =>
    have le := HsList.span_snd_length_le (fun x => p (HsChar.ofChar x)) cs
    simp only [HsList.span] at le
    have hit : p (HsChar.ofChar c) = true := by simpa [head, chars] using first
    simp only [span, chars, List.dropWhile_cons, hit, ite_true,
      String.toList_ofList, List.length_cons]
    omega

theorem break_shrinks (p : HsChar → Bool) (s : String)
    (nonempty : null s = false) (first : p (head s) = false) :
    («break» p s).2.toList.length < s.toList.length := by
  exact span_shrinks (fun c => !p c) s nonempty (by simp [first])

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
-- Rule H12.
def unpack (s : String) : List HsChar := s.toList.map HsChar.ofChar
def singleton (c : HsChar) : String := String.singleton (toChar c)
def cons (c : HsChar) (text : String) : String := singleton c ++ text
def foldl' {α : Type} (f : α → HsChar → α) (z : α) (s : String) : α := (unpack s).foldl f z
def any_ (p : HsChar → Bool) (s : String) : Bool := s.toList.any (fun c => p (HsChar.ofChar c))
def takeWhile (p : HsChar → Bool) (s : String) : String := (span p s).1
def stripStart (s : String) : String := String.ofList (s.toList.dropWhile isSpaceChar)
def stripEnd (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile isSpaceChar).reverse)
def splitAt (n : Int) (s : String) : String × String := (take n s, drop n s)
def isSuffixOf (a b : String) : Bool := a.toList.reverse.isPrefixOf b.toList.reverse
def takeWhileEnd (p : HsChar → Bool) (s : String) : String :=
  String.ofList ((s.toList.reverse.takeWhile (fun c => p (HsChar.ofChar c))).reverse)
def dropEnd (n : Int) (s : String) : String :=
  String.ofList (s.toList.take (s.toList.length - n.toNat))
-- The characters before the first occurrence of a nonempty needle, and the rest.
def breakOnList (needle : List Char) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if needle.isPrefixOf (c :: cs) then ([], c :: cs)
    else let r := breakOnList needle cs; (c :: r.1, r.2)
def breakOn (needle s : String) : String × String :=
  let r := breakOnList needle.toList s.toList
  (String.ofList r.1, String.ofList r.2)
-- breakOnEnd: breakOn on the reversed needle and text, reversed back.
def breakOnEnd (needle s : String) : String × String :=
  let r := breakOnList needle.toList.reverse s.toList.reverse
  (String.ofList r.2.reverse, String.ofList r.1.reverse)
-- The parts between the occurrences of a nonempty needle, from the left.
def splitOnList (needle : List Char) (xs : List Char) : List (List Char) :=
  match needle with
  | [] => [xs]
  | n :: ns => go (n :: ns) xs xs.length
where
  go (needle xs : List Char) : Nat → List (List Char)
    | 0 => [xs]
    | fuel + 1 =>
      let r := breakOnList needle xs
      if r.2.isEmpty then [r.1] else r.1 :: go needle (r.2.drop needle.length) fuel
def splitOn (needle s : String) : List String := (splitOnList needle.toList s.toList).map String.ofList
-- T.words: the maximal runs of characters that are not spaces.
def wordsList : List Char → List Char → List (List Char)
  | cur, [] => if cur.isEmpty then [] else [cur.reverse]
  | cur, c :: cs =>
    if isSpaceChar c then (if cur.isEmpty then [] else [cur.reverse]) ++ wordsList [] cs
    else wordsList (c :: cur) cs
def words (s : String) : List String := (wordsList [] s.toList).map String.ofList
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
def empty {κ ν : Type} : HsMap κ ν := ⟨[]⟩
def null {κ ν : Type} (m : HsMap κ ν) : Bool := m.pairs.isEmpty
def map {κ α β : Type} (f : α → β) (m : HsMap κ α) : HsMap κ β :=
  ⟨m.pairs.map (fun p => (p.1, f p.2))⟩
def lookup {κ ν : Type} [BEq κ] (k : κ) (m : HsMap κ ν) : Option ν :=
  (m.pairs.find? (·.1 == k)).map (·.2)
def member {κ ν : Type} [BEq κ] (k : κ) (m : HsMap κ ν) : Bool := m.pairs.any (·.1 == k)
def insertWith {κ ν : Type} [BEq κ] (f : ν → ν → ν) (k : κ) (v : ν) (m : HsMap κ ν) : HsMap κ ν :=
  if member k m then ⟨m.pairs.map (fun p => if p.1 == k then (k, f v p.2) else p)⟩ else ⟨m.pairs ++ [(k, v)]⟩
def insert {κ ν : Type} [BEq κ] (k : κ) (v : ν) (m : HsMap κ ν) : HsMap κ ν :=
  insertWith (fun new _ => new) k v m
-- containers' union is left-biased. The right-hand map only supplies keys
-- absent from the left; its colliding values never replace the left ones.
def union {κ ν : Type} [BEq κ] (left right : HsMap κ ν) : HsMap κ ν :=
  right.pairs.foldl (fun result p =>
    if member p.1 result then result else insert p.1 p.2 result) left
def fromList {κ ν : Type} [BEq κ] (xs : List (κ × ν)) : HsMap κ ν :=
  xs.foldl (fun m p => insert p.1 p.2 m) ⟨[]⟩
def fromListWith {κ ν : Type} [BEq κ] (f : ν → ν → ν) (xs : List (κ × ν)) : HsMap κ ν :=
  xs.foldl (fun m p => insertWith f p.1 p.2 m) ⟨[]⟩
def findWithDefault {κ ν : Type} [BEq κ] (d : ν) (k : κ) (m : HsMap κ ν) : ν :=
  (lookup k m).getD d
def keysSet {κ ν : Type} (m : HsMap κ ν) : HsSet κ := ⟨m.pairs.map (·.1)⟩
-- Rule H13: the pairs in the ascending order of the keys.
def insertByKey {κ ν : Type} [Ord κ] (p : κ × ν) : List (κ × ν) → List (κ × ν)
  | [] => [p]
  | q :: qs => if compare p.1 q.1 == .lt then p :: q :: qs else q :: insertByKey p qs
def toList {κ ν : Type} [Ord κ] (m : HsMap κ ν) : List (κ × ν) := m.pairs.foldr insertByKey []
def elems {κ ν : Type} [Ord κ] (m : HsMap κ ν) : List ν := (toList m).map (·.2)
-- Extensional equality, as containers' Eq.
def beq {κ ν : Type} [BEq κ] [BEq ν] (a b : HsMap κ ν) : Bool :=
  a.pairs.all (fun p => lookup p.1 b == some p.2) && b.pairs.all (fun p => member p.1 a)
instance {κ ν : Type} [BEq κ] [BEq ν] : BEq (HsMap κ ν) := ⟨beq⟩
end HsMap

namespace HsSet
def null {α : Type} (s : HsSet α) : Bool := s.elems.isEmpty
def member {α : Type} [BEq α] (x : α) (s : HsSet α) : Bool := s.elems.any (· == x)
def insert {α : Type} [BEq α] (x : α) (s : HsSet α) : HsSet α := if member x s then s else ⟨s.elems ++ [x]⟩
def fromList {α : Type} [BEq α] (xs : List α) : HsSet α := xs.foldl (fun s x => insert x s) ⟨[]⟩
def union {α : Type} [BEq α] (a b : HsSet α) : HsSet α := b.elems.foldl (fun s x => insert x s) a
def difference {α : Type} [BEq α] (a b : HsSet α) : HsSet α := ⟨a.elems.filter (fun x => !member x b)⟩
def intersection {α : Type} [BEq α] (a b : HsSet α) : HsSet α := ⟨a.elems.filter (member · b)⟩
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

-- H7: equality of show results must respect the extensional map/set
-- representation. Sort before Repr, as containers sorts before Show.
instance {κ ν : Type} [Ord κ] [Repr κ] [Repr ν] : Repr (HsMap κ ν) where
  reprPrec m prec := reprPrec (HsMap.toList m) prec
instance : Repr (HsSet String) where
  reprPrec s prec := reprPrec (HsSet.toList s) prec

/-! ## Termination of translated recursion -/

/-- Decreasing lengths of lists, for the hints: the equations of the
discriminants (and of the values of `span`) give the lengths. -/
macro "hs_decreasing" : tactic => `(tactic| (
  simp_wf <;>
  (try (have := HsList.span_eq_snd_length (by assumption))) <;>
  (try (have := HsList.break_cons_snd_length (by assumption) (by simp_all [HsList.elem, HsBase.or, HsBase.eq] <;> grind))) <;>
  (try simp_all +zetaDelta) <;>
  (try omega)))

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

-- Rule H7: `show` at a type other than Int or Integer is translated only where its
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

/-! ## Data.Array.Unboxed and Data.Text.Unsafe

Rules added for Peg.Runtime.Position (the positions of `here` in the
generated Peg.Grammar.SelfHosted):

- H14 `Data.Array.Unboxed`: a `UArray Int Int` is its lower bound and its
  elements in order. `listArray (lo, hi) xs` takes the first `hi - lo + 1`
  elements, `bounds` gives the bounds, and `arr ! i` the element at `i`.
  The translated code builds an array from exactly as many elements as its
  bounds hold and indexes it within them, where array's functions are
  defined.
- H15 `Data.Text.Unsafe`: a `Text` is the UTF-8 encoding of its scalar
  values (as rule R3 of RuntimeCore.lean). `lengthWord8` is the byte length;
  `iter t i` decodes the scalar that starts at the byte offset `i` and gives
  its width in bytes; `takeWord8 k` and `dropWord8 k` keep the bytes before
  and after the offset `k`. The translated code calls `iter` at a scalar
  boundary below the length and cuts at scalar boundaries, where the
  functions of text-2.1 are defined.
-/

structure HsUArray (α : Type) where
  lo : Int
  elems : List α
  deriving Inhabited

-- `maximum` at `[Int]` (rule H2), on a nonempty list.
def HsList.maximum : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl HsInt.max x

-- `either` (rule H9).
def HsEither.either {α β γ : Type} (f : α → γ) (g : β → γ) : Except α β → γ
  | .error a => f a
  | .ok b => g b

-- `T.empty` (rule H12).
def HsText.empty : String := ""

-- `T.foldr` (rule H12).
def HsText.foldr {α : Type} (f : HsChar → α → α) (z : α) (s : String) : α := (HsText.unpack s).foldr f z

namespace HsUArray
def listArray {α : Type} (b : Int × Int) (xs : List α) : HsUArray α := ⟨b.1, xs.take (b.2 - b.1 + 1).toNat⟩
def bounds {α : Type} (a : HsUArray α) : Int × Int := (a.lo, a.lo + a.elems.length - 1)
def index {α : Type} [Inhabited α] (a : HsUArray α) (i : Int) : α := a.elems.getD (i - a.lo).toNat default
end HsUArray

namespace HsTextU
structure Iter where
  Iter ::
  c : HsChar
  d : Int
  deriving Inhabited

def lengthWord8 (t : String) : Int := Int.ofNat t.utf8ByteSize
def iter (t : String) (i : Int) : Iter :=
  match t.toUTF8.utf8DecodeChar? i.toNat with
  | some ch => ⟨HsChar.ofChar ch, Int.ofNat ch.utf8Size⟩
  | none => ⟨default, 1⟩
def takeWord8 (k : Int) (t : String) : String := (String.fromUTF8? (t.toUTF8.extract 0 k.toNat)).getD ""
def dropWord8 (k : Int) (t : String) : String :=
  (String.fromUTF8? (t.toUTF8.extract k.toNat t.utf8ByteSize)).getD ""

/-- `iter` advances: the width is at least one byte. -/
theorem iter_width {t : String} {i : Int} {c : HsChar} {d : Int} (h : iter t i = Iter.Iter c d) : 1 ≤ d := by
  unfold iter at h
  split at h <;> cases h
  · next ch _ => have := Char.utf8Size_pos ch; simp only [Int.ofNat_eq_natCast]; omega
  · omega
end HsTextU
