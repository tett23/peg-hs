import Std

namespace PegHs.EscapePredicates

def digit (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 55)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87)
  else none

def value (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: rest => (digit c).bind fun d => value (16 * acc + d) rest

-- Positional value stated independently of the left-to-right accumulator.
inductive HexValue : List Char → Nat → Prop where
  | empty : HexValue [] 0
  | cons {c d rest n} (hd : digit c = some d) (hr : HexValue rest n) :
      HexValue (c :: rest) (d * 16 ^ rest.length + n)

theorem value_correct {cs : List Char} {acc out : Nat} :
    value acc cs = some out ↔ ∃ n, HexValue cs n ∧ out = acc * 16 ^ cs.length + n := by
  induction cs generalizing acc out with
  | nil =>
    constructor
    · intro h; cases h; exact ⟨0, .empty, by simp⟩
    · rintro ⟨_, h, eq⟩; cases h; simpa [value] using eq.symm
  | cons c cs ih =>
    constructor
    · intro h
      cases hd : digit c with
      | none => simp [value, hd] at h
      | some d =>
        obtain ⟨n, hn, eq⟩ := ih.mp (by simpa [value, hd] using h)
        exact ⟨_, .cons hd hn, by simp [eq, Nat.add_mul, Nat.pow_succ, Nat.mul_assoc,
          Nat.mul_comm, Nat.add_assoc]⟩
    · rintro ⟨_, hv, eq⟩; cases hv with
      | cons hd hr =>
        simp only [value, hd, Option.bind_some]
        apply ih.mpr
        exact ⟨_, hr, by simp_all [Nat.add_mul, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.add_assoc]⟩

def validHex (cs : List Char) : Bool :=
  !cs.isEmpty && (value 0 cs).any (· ≤ 0x10ffff)

theorem invariant1_validHex {cs : List Char} :
    validHex cs = true ↔ cs ≠ [] ∧ ∃ n, HexValue cs n ∧ n ≤ 0x10ffff := by
  cases h : value 0 cs with
  | none =>
    have impossible : ∀ n, ¬ HexValue cs n := by
      intro n hv
      have yes : value 0 cs = some n := value_correct.mpr ⟨n, hv, by simp⟩
      simp [h] at yes
    simp [validHex, h, impossible]
  | some n =>
    obtain ⟨m, hv, eq⟩ := value_correct.mp h
    simp at eq
    subst m
    have unique : ∀ v, HexValue cs v → v = n := by
      intro v vhex
      have yes : value 0 cs = some v := value_correct.mpr ⟨v, vhex, by simp⟩
      simp_all
    simp only [validHex, h, Option.any_some, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff, decide_eq_true_eq]
    exact and_congr_right fun _ => ⟨fun bound => ⟨n, hv, bound⟩,
      fun ⟨v, vhex, bound⟩ => unique v vhex ▸ bound⟩

-- Haskell Char can contain a surrogate; keep the decoded code point as Nat.
-- Only an unescaped hyphen carries the delimiter flag.
abbrev Token := Nat × Bool

def ranges : List Token → List (Nat × Nat)
  | (a, _) :: (_, true) :: (b, _) :: rest => (a,b) :: ranges rest
  | (a, _) :: rest => (a,a) :: ranges rest
  | [] => []

def nonEmptyRanges (ts : List Token) := (ranges ts).all fun r => decide (r.1 ≤ r.2)

theorem invariant1_nonEmptyRanges {ts : List Token} :
    nonEmptyRanges ts = true ↔ ∀ r ∈ ranges ts, ∃ c, r.1 ≤ c ∧ c ≤ r.2 := by
  simp only [nonEmptyRanges, List.all_eq_true, decide_eq_true_eq]
  exact forall_congr' fun r => forall_congr' fun _ =>
    ⟨fun h => ⟨r.1, Nat.le_refl _, h⟩, fun ⟨_, lo, hi⟩ => Nat.le_trans lo hi⟩

theorem invariant1_classItem (a b : Nat) (escapedA escapedB : Bool) :
    nonEmptyRanges [(a, escapedA), (45, true), (b, escapedB)] = true ↔ a ≤ b := by
  simp [nonEmptyRanges, ranges]
theorem invariant1_singleClassChar (c : Nat) (flag : Bool) :
    nonEmptyRanges [(c, flag)] = true := by simp [nonEmptyRanges, ranges]

example : validHex "10FfFf".toList = true := by decide
example : validHex "110000".toList = false := by decide
example : validHex "D800".toList = true := by decide
example : validHex [] = false := by decide

end PegHs.EscapePredicates
